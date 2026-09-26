#!/usr/bin/env python3
"""Accepted Gloas fork-choice runs projected onto the Lean FFG interpretation.

All links use block-body attestations and signer indices from the validation
state. BLS is disabled by the pyspec test-helper switch.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
import tomllib
from collections import defaultdict
from pathlib import Path

PIN = '13f391516352f61b3ac5dcaae5be1884d104f86a'
ROOT = Path(__file__).resolve().parents[4]
PREMISES = ROOT / 'FastConfirmationStatements/Premises'
INVENTORY = ROOT / 'scripts/conformance/contracts/inventory.toml'
NAMES = ('AcceptedBlockFFGState', 'FFGStateReadAgreement',
         'ScheduledFFGInterpretation', 'EventualCheckpointInclusion',
         'FFGStateAndCheckpointReadAgreement', 'EpochCheckpointProjectionLaws', 'IncludedLinkCheckpointAgreement')


def cp(value):
    return int(value.epoch), bytes(value.root).hex()


def reads_as(raw, semantic):
    return raw == semantic or raw[0] == semantic[0] == 0


def source_statements():
    rows = tomllib.loads(INVENTORY.read_text())['field']
    result = {}
    for row in rows:
        name = row['path']
        if not name.startswith(NAMES):
            continue
        source = (PREMISES / row['file']).read_text()
        structure, field = name.split('.', 1)
        body = re.search(r'(?m)^structure ' + structure + r'\b[\s\S]*?\bwhere\n([\s\S]*?)(?=\n(?:end|namespace|structure|/-!|section|def |abbrev |variable )|\Z)', source)
        if body is None:
            raise ValueError(name)
        match = re.search(r'(?m)^  ' + field + r'\s*:', body.group(1))
        if match is None:
            raise ValueError(name)
        tail = body.group(1)[match.start():]
        stop = re.search(r'(?m)^  (?:[A-Za-z_][\w]*\s*:|/--)', tail[len(match.group(0)):])
        result[name] = (tail if stop is None else tail[:len(match.group(0)) + stop.start()]).strip()
    for name, file, start, end in (
        ('ImportedBlockFinalizationLag', 'ScheduledExecutionConditions.lean', 'def ImportedBlockFinalizationLag', '\n\nend Execution'),
        ('GenesisOrNormalizedAnchor', 'NextSlotSafety.lean', 'def GenesisOrNormalizedAnchor', '\n\n/-- Assumptions')):
        source = (PREMISES / file).read_text()
        result[name] = source[source.index(start):source.index(end, source.index(start))].strip()
    return result


def setup(repo):
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
    if head != PIN:
        raise RuntimeError(f'pyspec pin mismatch: {head}')
    sys.path.insert(0, str(repo / 'tests/core/pyspec'))
    from eth_consensus_specs.utils import bls
    from eth_consensus_specs.gloas import minimal as spec
    from eth_consensus_specs.test.helpers.genesis import create_genesis_state
    from eth_consensus_specs.test.helpers.attestations import next_slots_with_attestations
    from eth_consensus_specs.test.helpers.state import state_transition_and_sign_block
    from eth_consensus_specs.test.helpers.block import build_empty_block
    from eth_consensus_specs.test.helpers.fork_choice import get_genesis_forkchoice_store_and_block
    bls.bls_active = False
    return spec, create_genesis_state, next_slots_with_attestations, state_transition_and_sign_block, build_empty_block, get_genesis_forkchoice_store_and_block


class Run:
    def __init__(self, name, spec, state, anchor_block, batches, *, later=False):
        self.name, self.spec = name, spec
        self.store = spec.get_forkchoice_store(state, anchor_block)
        self.anchor = cp(self.store.justified_checkpoint)
        self.anchor_root = bytes(spec.hash_tree_root(anchor_block)).hex()
        self.roots = [self.anchor_root]
        self.events = []
        self.blocks = {self.anchor_root: anchor_block}
        self.states = {self.anchor_root: state.copy()}
        self.parents = {self.anchor_root: None}
        self.votes = defaultdict(list)
        self.snapshots = []
        self.later = later
        self.errors = []
        for signed in batches:
            block = signed.message
            root = bytes(spec.hash_tree_root(block)).hex()
            parent = bytes(block.parent_root).hex()
            self.tick(int(block.slot))
            try:
                spec.on_block(self.store, signed)
            except Exception as exc:
                self.errors.append({'slot': int(block.slot), 'root': root, 'handler': 'on_block', 'error': repr(exc)})
                continue
            self.roots.append(root)
            self.events.append(root)
            self.blocks[root] = block
            self.states[root] = self.store.block_states[spec.Root(bytes.fromhex(root))].copy()
            self.parents[root] = parent
            for a in block.body.attestations:
                try:
                    self.votes[root].append((a, set(map(int, spec.get_attesting_indices(self.states[root], a)))))
                    spec.on_attestation(self.store, a, is_from_block=True)
                except Exception as exc:
                    self.errors.append({'slot': int(block.slot), 'root': root, 'handler': 'on_attestation', 'error': repr(exc)})
            self.snapshots.append({'slot': int(block.slot), 'root': root,
                                   'known': list(self.roots),
                                   'head': bytes(spec.get_head(self.store).root).hex(),
                                   'justified': cp(self.store.justified_checkpoint)})
        self._formed = {}
        self._links = {}
        self._eager = {}

    def tick(self, slot):
        self.spec.on_tick(self.store, int(self.store.genesis_time + slot * self.spec.config.SLOT_DURATION_MS // 1000))

    def ancestor(self, tip, root):
        while tip is not None:
            if tip == root:
                return True
            tip = self.parents[tip]
        return False

    def chain(self, tip):
        result = []
        while tip is not None:
            result.append(tip)
            tip = self.parents[tip]
        return list(reversed(result))

    def checkpoint(self, root, epoch):
        obj = self.spec.get_checkpoint_for_block(self.store, self.spec.Root(bytes.fromhex(root)), self.spec.Epoch(epoch))
        return cp(obj)

    def selector(self, root, name):
        state = self.states[root]
        if name.startswith('unrealized'):
            if root not in self._eager:
                eager = state.copy()
                self.spec.process_justification_and_finalization(eager)
                self._eager[root] = eager
            state = self._eager[root]
        raw = cp(state.current_justified_checkpoint if name.endswith('justified') else state.finalized_checkpoint)
        return self.anchor if raw[0] == 0 and self.anchor[0] == 0 else raw

    def formed_and_links(self, carrier):
        if carrier in self._formed:
            return self._formed[carrier], self._links[carrier]
        # Every signer must have an included body vote on this carrier chain.
        votes = defaultdict(set)
        for block_root in self.chain(carrier):
            for a, signers in self.votes[block_root]:
                source = cp(a.data.source)
                if source[0] == 0 and self.anchor[0] == 0:
                    source = self.anchor
                target = cp(a.data.target)
                if source[0] < target[0] and self.ancestor(target[1], source[1]) and self.ancestor(carrier, target[1]):
                    votes[source, target].update(signers)
        state = self.states[carrier]
        total = sum(int(v.effective_balance) for v in state.validators if self.spec.is_active_validator(v, self.spec.Epoch(0)))
        links = {pair: signers for pair, signers in votes.items()
                 if 3 * sum(int(state.validators[i].effective_balance) for i in signers) >= 2 * total}
        certified = {self.anchor}
        changed = True
        while changed:
            before = len(certified)
            certified.update(target for (source, target) in links if source in certified)
            changed = len(certified) != before
        # IncludedCheckpointEvidence also requires exact target ancestry and a
        # strictly earlier included target vote for non-anchor checkpoints.
        formed = {self.anchor}
        for c in certified - {self.anchor}:
            if not self.ancestor(carrier, c[1]):
                continue
            if any(cp(a.data.target) == c and int(a.data.slot) < int(self.blocks[carrier].slot)
                   for r in self.chain(carrier) for a, _ in self.votes[r]):
                formed.add(c)
        self._formed[carrier], self._links[carrier] = formed, links
        return formed, links

    def available(self, root):
        result = {}
        for carrier in self.chain(root):
            for c in self.formed_and_links(carrier)[0]:
                result.setdefault(c, carrier)
        return result

    def finalized_evidence(self, root, c):
        if c == self.anchor:
            return True
        for carrier in self.chain(root):
            formed, links = self.formed_and_links(carrier)
            if c in formed and any(source == c and target[0] == c[0] + 1 for source, target in links):
                return True
        return False

    def state_detail(self, root):
        state = self.states[root]
        return {'case': self.name, 'slot': int(self.blocks[root].slot), 'root': root,
                'realized_justified': cp(state.current_justified_checkpoint),
                'realized_finalized': cp(state.finalized_checkpoint),
                'unrealized_justified': self.selector(root, 'unrealized_justified'),
                'unrealized_finalized': self.selector(root, 'unrealized_finalized'),
                'store_unrealized_justified': cp(self.store.unrealized_justifications[self.spec.Root(bytes.fromhex(root))]),
                'anchor': self.anchor}


def make_runs(env, full):
    spec, genesis, next_slots, sign, build, genesis_store = env
    def start():
        state = genesis(spec, [32 * 10**9] * 64, 32 * 10**9)
        _, block = genesis_store(spec, state)
        return state, block
    runs = []
    state, anchor = start()
    _, blocks, state = next_slots(spec, state, 48 if full else 17, True, False)
    runs.append(Run('full-epoch-6' if full else 'full-fast', spec, genesis(spec, [32 * 10**9] * 64, 32 * 10**9), anchor, blocks))
    # The first 16 blocks form the review's accepted prefix.
    runs.append(Run('review-slot-16', spec, genesis(spec, [32 * 10**9] * 64, 32 * 10**9), anchor, blocks[:16]))
    if not full:
        return runs
    state, anchor = start()
    _, first, state = next_slots(spec, state, 15, False, False)
    def above_two_thirds(slot, index, indices):
        ordered = sorted(indices)
        # Sixteen disjoint committees of four: 11*3 + 5*2 = 43 of 64.
        take = 3 if int(slot) < 20 or (int(slot) == 20 and int(index) == 0) else 2
        return set(ordered[:take])
    _, late, state = next_slots(spec, state, 9, False, True, above_two_thirds)
    runs.append(Run('late-two-thirds', spec, genesis(spec, [32 * 10**9] * 64, 32 * 10**9), anchor, first + late))
    state, anchor = start()
    _, first, state = next_slots(spec, state, 7, True, False)
    spec.process_slots(state, 15)
    bridge = build(spec, state, slot=16)
    bridge_signed = sign(spec, state, bridge)
    _, tail, state = next_slots(spec, state, 16, True, False)
    runs.append(Run('skipped-epoch', spec, genesis(spec, [32 * 10**9] * 64, 32 * 10**9), anchor, first + [bridge_signed] + tail))
    state, anchor = start()
    _, branch_a, _ = next_slots(spec, state, 16, True, False)
    branch_state = state.copy()
    fork_block = build(spec, branch_state, slot=1)
    fork_block.body.graffiti = spec.Bytes32(b'projection-fork'.ljust(32, b'\0'))
    fork_first = sign(spec, branch_state, fork_block)
    _, branch_tail, _ = next_slots(spec, branch_state, 15, False, False)
    interleaved = []
    for a, b in zip(branch_a, [fork_first] + branch_tail):
        interleaved.extend((a, b))
    runs.append(Run('two-forks', spec, state, anchor, interleaved))
    state, anchor = start()
    _, blocks, state = next_slots(spec, state, 24, True, False)
    runs.append(Run('later-anchor-out-of-scope', spec, state, blocks[-1].message, [], later=True))
    full_run, review, delayed, skipped, forks, later_run = runs
    if not (int(full_run.blocks[full_run.roots[-1]].slot)//8 >= 6 and
            full_run.selector(full_run.roots[-1], 'realized_justified')[0] > 0 and
            full_run.selector(full_run.roots[-1], 'realized_finalized')[0] > 0):
        raise AssertionError('full-participation fixture did not move justification and finality')
    if not (review.selector(review.roots[-1], 'realized_justified')[0] == 0 and
            review.selector(review.roots[-1], 'unrealized_justified')[0] == 1):
        raise AssertionError('review slot-16 gap missing')
    delayed_formed = [(int(delayed.blocks[r].slot), c) for r in delayed.roots
                      for c in delayed.formed_and_links(r)[0] if c[0] == 1]
    delayed_votes = [(int(delayed.blocks[r].slot), a, signers) for r in delayed.roots
                     for a, signers in delayed.votes[r] if int(a.data.target.epoch) == 1]
    if not (delayed_formed and min(slot for slot, _ in delayed_formed) >= 16 and
            all(slot >= 16 for slot, _, _ in delayed_votes) and
            len(set().union(*(signers for _, _, signers in delayed_votes))) == 43):
        raise AssertionError(f'delayed fixture: formed={delayed_formed[:2]}, votes={[(x, len(s)) for x, _, s in delayed_votes]}, unique={len(set().union(*(signers for _, _, signers in delayed_votes)))}')
    if any(8 <= int(skipped.blocks[r].slot) < 16 for r in skipped.events):
        raise AssertionError('skipped epoch has a block')
    fork_tips = [r for r in forks.events if int(forks.blocks[r].slot) == 16]
    if len(fork_tips) != 2 or len({sum(len(forks.votes[r]) for r in forks.chain(tip)) for tip in fork_tips}) != 2:
        raise AssertionError('two-fork inclusion fixture missing')
    if later_run.anchor[0] == 0:
        raise AssertionError('later anchor fixture missing')
    return runs


def check_run(run, statements):
    results = []
    def record(name, ok, detail, *, scope='checked'):
        results.append({'field': name, 'status': ('OUT_OF_SCOPE' if run.later and not ok else ('PASS' if ok else 'FAIL')), 'scope': scope,
                        'state': detail, 'statement': statements[name]})
    def each(name, evaluations):
        fails = [detail for ok, detail in evaluations if not ok]
        record(name, not fails, fails[0] if fails else {'case': run.name, 'checked': len(evaluations)},
               scope='checked' if evaluations else 'no instances')
    root_set = set(run.roots)
    all_roots = run.roots
    imported = run.events
    record('ScheduledFFGInterpretation.anchor', run.anchor_root == run.anchor[1], {'case': run.name, 'anchor': run.anchor, 'anchor_root': run.anchor_root})
    record('GenesisOrNormalizedAnchor', run.anchor[0] == 0 or
           (cp(run.states[run.anchor_root].current_justified_checkpoint) == run.anchor and
            cp(run.states[run.anchor_root].finalized_checkpoint) == run.anchor),
           {'case': run.name, 'anchor': run.anchor, 'state': run.state_detail(run.anchor_root)})
    # The state bundle is assessed after its component laws.
    for field in ('includedAttestations', 'checkpoint_evidence_in_block', 'checkpoint_at_epoch',
                  'realized_justified', 'unrealized_justified', 'realized_finalized', 'unrealized_finalized'):
        record('AcceptedBlockFFGState.' + field, True,
               {'case': run.name, 'mapping': field, 'accepted_roots': len(all_roots),
                'body_votes': sum(map(len, run.votes.values()))}, scope='construction')
    for field in ('checkpoint_epoch', 'formed_carrier_accepted', 'formed_evidence',
                  'realized_justified_mem', 'unrealized_justified_mem', 'realized_finalized_mem',
                  'unrealized_finalized_mem', 'realized_justified_anchor_or_before',
                  'realized_justified_max', 'unrealized_justified_max',
                  'available_checkpoint_epoch_le_block', 'realized_finalized_evidence',
                  'unrealized_finalized_evidence', 'realized_finalized_epoch_le_realized_justified',
                  'unrealized_finalized_epoch_le_unrealized_justified'):
        samples = []
        for root in all_roots:
            slot = int(run.blocks[root].slot)
            epoch = slot // int(run.spec.SLOTS_PER_EPOCH)
            available = run.available(root)
            formed, links = run.formed_and_links(root)
            rj = run.selector(root, 'realized_justified')
            uj = run.selector(root, 'unrealized_justified')
            rf = run.selector(root, 'realized_finalized')
            uf = run.selector(root, 'unrealized_finalized')
            detail = run.state_detail(root)
            if field == 'checkpoint_epoch':
                for e in range(run.anchor[0], epoch + 3):
                    c = run.checkpoint(root, e)
                    samples.append((c[0] == e, {**detail, 'epoch': e, 'checkpoint': c}))
                continue
            if field == 'formed_carrier_accepted':
                samples += [(root in root_set, {**detail, 'formed': c}) for c in formed]
            elif field == 'formed_evidence':
                samples += [(c == run.anchor or (c in available and run.ancestor(root, c[1])),
                             {**detail, 'formed': c}) for c in formed]
            elif field.endswith('_mem'):
                c = {'realized_justified_mem': rj, 'unrealized_justified_mem': uj,
                     'realized_finalized_mem': rf, 'unrealized_finalized_mem': uf}[field]
                samples.append((c in available, {**detail, 'checkpoint': c, 'available': [{'checkpoint': c, 'carrier': carrier} for c, carrier in available.items()]}))
            elif field == 'realized_justified_anchor_or_before':
                samples.append((rj == run.anchor or rj[0] < epoch, detail))
            elif field == 'realized_justified_max':
                samples += [(c[0] >= epoch or c[0] <= rj[0], {**detail, 'available': c,
                             'carrier': carrier}) for c, carrier in available.items()]
            elif field == 'unrealized_justified_max':
                samples += [(c[0] <= uj[0], {**detail, 'available': c,
                             'carrier': carrier}) for c, carrier in available.items()]
            elif field == 'available_checkpoint_epoch_le_block':
                samples += [(c[0] <= epoch, {**detail, 'available': c,
                             'carrier': carrier}) for c, carrier in available.items()]
            elif field == 'realized_finalized_evidence':
                samples.append((run.finalized_evidence(root, rf), {**detail, 'checkpoint': rf}))
            elif field == 'unrealized_finalized_evidence':
                samples.append((run.finalized_evidence(root, uf), {**detail, 'checkpoint': uf}))
            elif field == 'realized_finalized_epoch_le_realized_justified':
                samples.append((rf[0] <= rj[0], detail))
            elif field == 'unrealized_finalized_epoch_le_unrealized_justified':
                samples.append((uf[0] <= uj[0], detail))
        each('AcceptedBlockFFGState.' + field, samples)
    # Read agreements use independent store reads against the projected selectors.
    for kind in ('gj', 'gf', 'gu', 'guf'):
        field = {'gj':'realized_justified', 'gf':'realized_finalized',
                 'gu':'unrealized_justified', 'guf':'unrealized_finalized'}[kind]
        for label, roots in (('genesis', [run.anchor_root]), ('transition', imported)):
            samples = []
            for root in roots:
                raw = run.states[root]
                if kind in ('gu', 'guf'):
                    raw = raw.copy()
                    run.spec.process_justification_and_finalization(raw)
                checkpoint = cp(raw.current_justified_checkpoint if kind in ('gj','gu') else raw.finalized_checkpoint)
                value = run.selector(root, field)
                samples.append((reads_as(checkpoint, value), {**run.state_detail(root), 'raw': checkpoint, 'selector': value}))
            each(f'FFGStateReadAgreement.{label}_{kind}', samples)
    anchor_root = run.spec.Root(bytes.fromhex(run.anchor_root))
    each('FFGStateReadAgreement.genesis_unrealized_justification',
         [(reads_as(cp(run.store.unrealized_justifications[anchor_root]), run.selector(run.anchor_root,'unrealized_justified')),
           run.state_detail(run.anchor_root))])
    samples = []
    for root in imported:
        raw = cp(run.states[root].finalized_checkpoint)
        samples.append((reads_as(raw, run.anchor) or raw[0] + 2 <= int(run.blocks[root].slot)//8,
                        {**run.state_detail(root), 'raw_finalized': raw}))
    each('ImportedBlockFinalizationLag', samples)
    # Projection laws and exact links use accepted roots in the final prefix.
    accept_samples, comp_samples, carrier_samples, endpoint_samples = [], [], [], []
    for root in all_roots:
        epoch = int(run.blocks[root].slot)//8
        for e in range(run.anchor[0], epoch + 3):
            c = run.checkpoint(root, e)
            accept_samples.append((c[1] in root_set, {**run.state_detail(root), 'checkpoint': c}))
            for source in range(run.anchor[0], e + 1):
                left = run.checkpoint(c[1], source) if c[1] in root_set else None
                right = run.checkpoint(root, source)
                comp_samples.append((left == right, {**run.state_detail(root), 'source_epoch': source,
                                                      'target_epoch': e, 'left': left, 'right': right}))
        _, links = run.formed_and_links(root)
        certified = run.formed_and_links(root)[0]
        for (source, target), signers in links.items():
            if source not in certified:
                continue
            detail = {**run.state_detail(root), 'source': source, 'target': target,
                      'signers': sorted(signers)}
            carrier_samples.append((root in root_set, detail))
            endpoint_samples.append((source == run.checkpoint(root, source[0]) and
                                     target == run.checkpoint(root, target[0]), detail))
    each('EpochCheckpointProjectionLaws.checkpoint_root_accepted', accept_samples)
    each('EpochCheckpointProjectionLaws.checkpoint_comp', comp_samples)
    each('IncludedLinkCheckpointAgreement.carrier_accepted', carrier_samples)
    each('IncludedLinkCheckpointAgreement.endpoints_on_carrier', endpoint_samples)
    reflection = []
    available_reflection = []
    for root in all_roots:
        epoch = int(run.blocks[root].slot)//8
        for e in range(run.anchor[0], epoch + 3):
            reflection.append({**run.state_detail(root), 'epoch': e, 'checkpoint': run.checkpoint(root, e)})
        for c, carrier in run.available(root).items():
            available_reflection.append((c == run.checkpoint(root, c[0]),
                                         {**run.state_detail(root), 'checkpoint': c, 'carrier': carrier}))
    record('FFGStateAndCheckpointReadAgreement.checkpoint_of_known', True,
           {'case': run.name, 'mapped_reads': len(reflection), 'first': reflection[0]}, scope='construction: C is the fork-choice read')
    each('FFGStateAndCheckpointReadAgreement.available_checkpoint_checkpoint_of_known', available_reflection)
    state_failures = [r for r in results if r['field'].startswith('AcceptedBlockFFGState.') and r['status'] in ('FAIL','OUT_OF_SCOPE')]
    record('ScheduledFFGInterpretation.state', not state_failures,
           state_failures[0]['state'] if state_failures else {'case': run.name, 'state_laws': 22})
    coherence_failures = [r for r in results if r['field'].startswith(('FFGStateReadAgreement.',
                          'FFGStateAndCheckpointReadAgreement.')) and r['status'] in ('FAIL','OUT_OF_SCOPE')]
    record('ScheduledFFGInterpretation.coherence', not coherence_failures,
           coherence_failures[0]['state'] if coherence_failures else {'case': run.name, 'read_agreements': 11})
    consequence = []
    for base in all_roots:
        for e in range(int(run.blocks[base].slot)//8, min(6, max(int(run.blocks[r].slot) for r in all_roots)//8 - 1)):
            c = run.checkpoint(base, e)
            cutoff = 8*(e+2)
            for snap in run.snapshots:
                if snap['slot'] < cutoff or base not in snap['known']:
                    continue
                candidates = [tip for tip in snap['known'] if run.ancestor(tip, base) and
                              int(run.blocks[tip].slot) < cutoff and c in run.available(tip)]
                consequence.append({'base': base, 'epoch': e, 'view_slot': snap['slot'],
                                    'checkpoint': c, 'descendant_found': bool(candidates)})
    results.append({'field': 'EventualCheckpointInclusion.included', 'status': 'NOT_ESTABLISHED',
                    'scope': 'antecedent not established; sampled consequence only',
                    'state': {'case': run.name, 'sampled_consequents': len(consequence),
                              'consequents_true': sum(x['descendant_found'] for x in consequence),
                              'first_false': next((x for x in consequence if not x['descendant_found']), None),
                              'reason': 'SourceTargetSupportThroughoutEpoch needs every honest view, received vote history, and D_b slashing state.'},
                    'statement': statements['EventualCheckpointInclusion.included']})
    return results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--full', action='store_true')
    args = parser.parse_args()
    start = time.monotonic()
    statements = source_statements()
    runs = make_runs(setup(args.repo), args.full)
    results = [r for run in runs for r in check_run(run, statements)]
    data = {'pin': PIN, 'bls_active': False, 'full': args.full,
            'runtime_seconds': round(time.monotonic()-start, 3),
            'runs': [{'name': run.name, 'blocks': len(run.roots), 'max_slot': max(int(run.blocks[r].slot) for r in run.roots),
                      'handler_errors': run.errors, 'checkpoints': [run.state_detail(r) for r in run.roots
                                                                      if int(run.blocks[r].slot) % 8 == 0]} for run in runs],
            'results': results}
    args.output.write_text(json.dumps(data, indent=2) + '\n')
    failures = sorted({r['field'] for r in results if r['status']=='FAIL'})
    print(f'projection: {len(runs)} runs, {len(results)} field checks, {data["runtime_seconds"]} s')
    print('findings:', ', '.join(failures) if failures else 'none')
    return 0  # Findings are recorded for Lean repair; they do not hide later probes.


if __name__ == '__main__':
    raise SystemExit(main())
