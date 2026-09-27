#!/usr/bin/env python3
"""Check finite premise fields on one 100-validator mixed-balance pyspec run.

This is a falsification check, not a proof of the full execution bundle. It
reuses the accepted-block FFG projection and tests finite registry, committee,
and economic fields against the same genesis-to-epoch-6 run. A second genesis
with 128 validators of 32 ETH checks only `estimate_sound`, split into
within-epoch and cross-boundary spans.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'projection'))
sys.path.insert(0, str(HERE.parent / 'concrete'))
import run as projection  # noqa: E402
import run_differential as differential  # noqa: E402


def epoch_ends_fit(slots_per_epoch):
    return slots_per_epoch > 0 and 2**64 % slots_per_epoch == 0


EXPECTED_ESTIMATE_FAILURE_FINGERPRINT = 'c0247ff02146c874e9e3bbac1966a71492e71f66d9055f0e25be9563a1e2e6a5'


def retained_projection_rows(spec, run, overrides=None):
    """Differential rows for every accepted block of the run.

    Each row holds the retained FFG fields of the parent post-state, the wire
    fields of the block, and the committees that the block attestations read.
    Roots and hashes become consistent integer labels; the zero root is 0. The
    header root is the root of the latest header after `process_slot` fills
    its state root, as Python `process_block_header` reads it."""
    labels = {bytes(32): 0}

    def label(value):
        return labels.setdefault(bytes(value), len(labels))

    def checkpoint(value):
        return [int(value.epoch), label(value.root)]

    def header_root(state):
        header = state.latest_block_header.copy()
        if header.state_root == spec.Root():
            header.state_root = spec.hash_tree_root(state)
        return label(spec.hash_tree_root(header))

    def retained(state):
        return {
            'genesis_time': int(state.genesis_time),
            'slot': int(state.slot),
            'header_slot': int(state.latest_block_header.slot),
            'header_proposer_index': int(state.latest_block_header.proposer_index),
            'header_parent_root': label(state.latest_block_header.parent_root),
            'header_root': header_root(state),
            'validators': registry(state),
            'bits': [bool(x) for x in state.justification_bits],
            'previous_justified': checkpoint(state.previous_justified_checkpoint),
            'current_justified': checkpoint(state.current_justified_checkpoint),
            'finalized': checkpoint(state.finalized_checkpoint),
            'previous_participation': [int(x) for x in state.previous_epoch_participation],
            'current_participation': [int(x) for x in state.current_epoch_participation],
            'block_roots': [label(x) for x in state.block_roots],
            'availability': [bool(x) for x in state.execution_payload_availability],
            'latest_block_hash': label(state.latest_block_hash),
            'latest_bid_block_hash': label(state.latest_execution_payload_bid.block_hash),
        }

    def registry(state):
        return [{'effective_balance': int(v.effective_balance), 'slashed': bool(v.slashed),
                 'activation_epoch': int(v.activation_epoch), 'exit_epoch': int(v.exit_epoch)}
                for v in state.validators]

    rows, expected = [], []
    for root in run.events:
        block = run.blocks[root]
        body = block.body
        # The fixture has no operation that the projection erases.
        if (body.proposer_slashings or body.attester_slashings or body.voluntary_exits
                or body.bls_to_execution_changes or body.deposits):
            raise RuntimeError(f'block {root} has an erased operation')
        pre = overrides[root][0] if overrides and root in overrides else run.states[run.parents[root]]
        at_slot = pre.copy()
        spec.process_slots(at_slot, block.slot)
        bid = body.signed_execution_payload_bid.message
        requests = body.parent_execution_requests
        committees, counts = {}, {}
        votes = []
        for a in body.attestations:
            slot = int(a.data.slot)
            epoch = int(spec.compute_epoch_at_slot(a.data.slot))
            count = int(spec.get_committee_count_per_slot(at_slot, spec.Epoch(epoch)))
            counts[epoch] = count
            for index in range(count):
                committees[slot, index] = [int(i) for i in spec.get_beacon_committee(
                    at_slot, a.data.slot, spec.CommitteeIndex(index))]
            votes.append({'aggregation_bits': [bool(x) for x in a.aggregation_bits],
                          'committee_bits': [bool(x) for x in a.committee_bits],
                          'data': {'slot': slot, 'index': int(a.data.index),
                                   'beacon_block_root': label(a.data.beacon_block_root),
                                   'source': checkpoint(a.data.source),
                                   'target': checkpoint(a.data.target)}})
        rows.append({
            'name': f'accepted_slot_{int(block.slot)}', 'action': 'transition',
            'state': {**retained(pre), 'validators': registry(pre)},
            'oracle_accept': True,
            'schedule': {'committees': [[s, i, m] for (s, i), m in sorted(committees.items())],
                         'counts': [[e, n] for e, n in sorted(counts.items())]},
            'block': {'slot': int(block.slot), 'parent_root': label(block.parent_root),
                      'proposer_index': int(block.proposer_index),
                      'root': label(spec.hash_tree_root(block)),
                      'parent_block_hash': label(bid.parent_block_hash),
                      'block_hash': label(bid.block_hash),
                      'parent_requests_empty': requests == spec.ExecutionRequests(),
                      'parent_requests_match': spec.hash_tree_root(requests)
                      == at_slot.latest_execution_payload_bid.execution_requests_root,
                      'deposit_count': len(body.deposits), 'attestations': votes},
        })
        post = overrides[root][1] if overrides and root in overrides else run.states[root]
        # The Lean state keeps the registry of the fixed scope, so a Python
        # registry change is a difference of the retained projection.
        expected.append({'ok': True, 'value': retained(post)})
    return rows, expected


def slot_committees(spec, run, slots):
    """Read each epoch from a state in that epoch of this accepted run."""
    committees = {}
    for slot in range(slots):
        epoch = slot // int(spec.SLOTS_PER_EPOCH)
        root = (run.anchor_root if epoch == 0 else next(root for root in run.events
                    if int(run.states[root].slot) == epoch * int(spec.SLOTS_PER_EPOCH)))
        state = run.states[root]
        members = set()
        for index in range(int(spec.get_committee_count_per_slot(state, spec.Epoch(epoch)))):
            members.update(map(int, spec.get_beacon_committee(
                state, spec.Slot(slot), spec.CommitteeIndex(index))))
        committees[slot] = members
    return committees


def estimate_spans(spec, state, committees):
    """`estimate_sound` on every slot span [a, b], split into within-epoch
    spans (idealization part (i), equal slot-committee weights) and
    cross-boundary spans (part (ii), the pro-rated estimate of a perfectly
    mixed reshuffle)."""
    spe = int(spec.SLOTS_PER_EPOCH)
    total = int(spec.get_total_active_balance(state))
    registry = state.validators
    result = {kind: {'checks': 0, 'failures': []} for kind in ('within_epoch', 'cross_boundary')}
    slots = sorted(committees)
    for start, a in enumerate(slots):
        members = set()
        for b in slots[start:]:
            members.update(committees[b])
            actual = sum(int(registry[i].effective_balance) for i in members)
            estimate = int(spec.estimate_committee_weight_between_slots(
                total, spec.Slot(a), spec.Slot(b)))
            kind = 'within_epoch' if a // spe == b // spe else 'cross_boundary'
            result[kind]['checks'] += 1
            if actual > estimate:
                result[kind]['failures'].append({'a': a, 'b': b, 'weight': actual,
                                                 'estimate': estimate})
    return result


def epoch_registry_change(spec, run):
    """Negative control for the epoch-step applicability condition.

    The bridge keeps every validator record fixed, so it represents a Python
    run only if no epoch step changes a record in the horizon. Lower the
    balance of validator 0 below the downward hysteresis threshold before the
    first epoch-crossing block at or after slot 16. Python
    `process_effective_balance_updates` then lowers its effective balance, and
    the retained-projection comparison must report the registry change."""
    root = next(r for r in run.events
                if int(run.blocks[r].slot) >= 16 and int(run.blocks[r].slot) % 8 == 0)
    pre = run.states[run.parents[root]].copy()
    # Fix the header state root first, so that the parent root of the block
    # still matches after the balance change.
    pre.latest_block_header.state_root = spec.hash_tree_root(pre)
    pre.balances[0] = spec.Gwei(int(pre.validators[0].effective_balance)
                                - int(spec.EFFECTIVE_BALANCE_INCREMENT) // 2)
    post = pre.copy()
    spec.state_transition(post, spec.SignedBeaconBlock(message=run.blocks[root]),
                          validate_result=False)
    return {'slot': int(run.blocks[root].slot), 'root': root,
            'pre': pre, 'post': post,
            'before': int(pre.validators[0].effective_balance),
            'after': int(post.validators[0].effective_balance)}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    spec, genesis, next_slots, _, _, genesis_store = projection.setup(args.repo)
    balances = [(32 + i % 4) * 10**9 for i in range(100)]
    base = genesis(spec, balances, spec.MIN_ACTIVATION_BALANCE)
    _, anchor = genesis_store(spec, base)
    _, blocks, tail = next_slots(spec, base, 48, True, False)
    run = projection.Run('mixed-100-genesis-to-epoch-6', spec,
                         genesis(spec, balances, spec.MIN_ACTIVATION_BALANCE), anchor, blocks)
    if run.errors or len(run.roots) != 49 or int(tail.slot) < 48:
        raise RuntimeError(f'fixture did not import 48 normal-participation blocks: {run.errors}')
    results = []

    def field(name: str, passed: bool, checks: int, detail: dict | None = None) -> None:
        results.append({'field': name, 'status': 'PASS' if passed else 'FAIL',
                        'checks': checks, 'first_failure': detail if not passed else None})

    anchor_state = run.states[run.anchor_root]
    registry = anchor_state.validators
    horizon = 7
    slots_per_epoch = int(spec.SLOTS_PER_EPOCH)
    increment = int(spec.EFFECTIVE_BALANCE_INCREMENT)
    active = {e: set(map(int, spec.get_active_validator_indices(anchor_state, spec.Epoch(e))))
              for e in range(horizon)}
    field('StaticValidatorSet.genesis_within_horizon', 0 < horizon, 1)
    field('StaticValidatorSet.activity_constant', all(active[e] == active[0] for e in active), horizon)
    def registry_view(state):
        return tuple((int(v.effective_balance), bool(v.slashed), int(v.activation_epoch),
                      int(v.exit_epoch)) for v in state.validators)
    ref = registry_view(anchor_state)
    changed = next((root for root, state in run.states.items() if registry_view(state) != ref), None)
    field('BeaconExternalsPremises.registry_static_in_horizon', changed is None,
          len(run.states), {'root': changed} if changed else None)
    field('ScheduledFCRCallPremises.balance_floor',
          sum(int(registry[i].effective_balance) for i in active[0]) >= 2 * increment, 1)
    field('SafetyPremises.slots_per_epoch_gt_one', slots_per_epoch > 1, 1)
    field('SafetyPremises.epoch_ends_fit',
          epoch_ends_fit(slots_per_epoch), 1)
    if epoch_ends_fit(7) or not epoch_ends_fit(8):
        raise RuntimeError('epoch_ends_fit boundary controls failed')
    field('finite_horizon_within_uint64', horizon * slots_per_epoch < 2**64, 1)
    field('NextSlotSafetyPremises.anchor_boundary', int(anchor.slot) % slots_per_epoch == 0, 1)
    field('NextSlotSafetyPremises.anchor_eq', run.anchor[1] == run.anchor_root, 1)
    field('NextSlotSafetyPremises.anchor_state_checkpoints',
          run.anchor[0] == 0 and int(anchor_state.current_justified_checkpoint.epoch) == 0
          and int(anchor_state.finalized_checkpoint.epoch) == 0, 1)
    field('BeaconExternalsPremises.anchor_state_checkpoint_epoch',
          int(anchor_state.current_justified_checkpoint.epoch) <= int(anchor_state.slot) // slots_per_epoch
          and int(anchor_state.finalized_checkpoint.epoch) <= int(anchor_state.slot) // slots_per_epoch, 1)
    field('SafetyPremises.whole_seconds', int(spec.config.SLOT_DURATION_MS) % 1000 == 0, 1)
    field('ByzantineWeightPremises.effective_balance_quantized',
          all(int(v.effective_balance) % increment == 0 for v in registry), len(registry))
    # T laws sampled on accepted keyed states of this same execution.
    slot_target_results = []
    pjf_results = []
    same_epoch_results = []
    one_boundary_results = []
    same_target_results = []
    for root, state in run.states.items():
        slot = int(state.slot)
        epoch = slot // slots_per_epoch
        next_slot = slot + 1
        processed = state.copy()
        spec.process_slots(processed, spec.Slot(next_slot))
        slot_target_results.append((int(processed.slot) == next_slot, root))
        eager = state.copy()
        spec.process_justification_and_finalization(eager)
        if int(state.current_justified_checkpoint.epoch) <= epoch:
            pjf_results.append((int(eager.current_justified_checkpoint.epoch) <= epoch, root))
        if next_slot // slots_per_epoch == epoch:
            same_epoch_results.append((projection.cp(processed.current_justified_checkpoint)
                                       == projection.cp(state.current_justified_checkpoint), root))
        boundary = (epoch + 1) * slots_per_epoch
        if boundary < horizon * slots_per_epoch:
            at_boundary = state.copy()
            spec.process_slots(at_boundary, spec.Slot(boundary))
            one_boundary_results.append((projection.cp(at_boundary.current_justified_checkpoint)
                                         == projection.cp(eager.current_justified_checkpoint), root))
            after_boundary = state.copy()
            spec.process_slots(after_boundary, spec.Slot(boundary + 1))
            same_target_results.append((projection.cp(at_boundary.current_justified_checkpoint)
                                        == projection.cp(after_boundary.current_justified_checkpoint), root))
    for name, cases in (
        ('BeaconExternalsPremises.process_slots_slot', slot_target_results),
        ('BeaconExternalsPremises.pjf_checkpoint_epoch', pjf_results),
        ('Phase0SourceCoherence.process_slots_current_justified', same_epoch_results),
        ('Phase0BoundarySourceCoherence.process_slots_one_boundary', one_boundary_results),
        ('Phase0BoundarySourceCoherence.process_slots_same_target_epoch', same_target_results),
    ):
        failed = next((root for ok, root in cases if not ok), None)
        field(name, failed is None and bool(cases), len(cases), {'root': failed} if failed else None)
    committees = slot_committees(spec, run, 48)
    unique = all(sum(len(committees[s]) for s in range(e*slots_per_epoch, (e+1)*slots_per_epoch))
                 == len(set().union(*(committees[s] for s in range(e*slots_per_epoch, (e+1)*slots_per_epoch))))
                 for e in range(6))
    field('ConcreteExternalsPremises.committee_assignment_unique', unique, 6)
    covered = all(active[e] <= set().union(*(committees[s] for s in range(e*slots_per_epoch, (e+1)*slots_per_epoch)))
                  for e in range(6))
    field('ConcreteExternalsPremises.committee_coverage', covered, 6)
    member_active = all(committees[s] <= active[s // slots_per_epoch] for s in committees)
    field('ConcreteExternalsPremises.committee_members_active', member_active, len(committees))
    mixed = estimate_spans(spec, anchor_state, committees)
    estimate_failures = mixed['within_epoch']['failures'] + mixed['cross_boundary']['failures']
    estimate_failures.sort(key=lambda f: (f['a'], f['b']))
    span_checks = mixed['within_epoch']['checks'] + mixed['cross_boundary']['checks']
    field('ByzantineWeightPremises.estimate_sound', not estimate_failures,
          span_checks, estimate_failures[0] if estimate_failures else None)
    # All validators in this run are honest, so the per-span fault bound holds
    # vacuously: zero Byzantine weight cannot exceed a nonnegative threshold.
    field('ByzantineWeightPremises.span_fraction', True, span_checks)
    # Part (i) of the committee-sampling idealization on a real pyspec genesis
    # with equal balances: within-epoch spans must pass. Cross-boundary spans
    # fail by part (ii): the real reshuffle is one sample, and the pro-rated
    # estimate is the expected overlap.
    uniform_state = genesis(spec, [32 * 10**9] * 128, spec.MIN_ACTIVATION_BALANCE)
    _, uniform_anchor = genesis_store(spec, uniform_state)
    _, uniform_blocks, _ = next_slots(spec, uniform_state, 48, True, False)
    uniform_run = projection.Run('uniform-128-genesis-to-epoch-6', spec,
                                 genesis(spec, [32 * 10**9] * 128, spec.MIN_ACTIVATION_BALANCE),
                                 uniform_anchor, uniform_blocks)
    if uniform_run.errors or len(uniform_run.roots) != 49:
        raise RuntimeError(f'uniform fixture did not import 48 blocks: {uniform_run.errors}')
    uniform = estimate_spans(spec, uniform_run.states[uniform_run.anchor_root],
                             slot_committees(spec, uniform_run, 48))
    for kind in ('within_epoch', 'cross_boundary'):
        failures = uniform[kind]['failures']
        field(f'ByzantineWeightPremises.estimate_sound.uniform_{kind}', not failures,
              uniform[kind]['checks'], failures[0] if failures else None)
    # A5: the retained projection of every accepted block. The Lean concrete
    # transition, with an accepting oracle and the committees that the block
    # reads, must give the retained fields of the Python post-state.
    rows, expected = retained_projection_rows(spec, run)
    actual = differential.lean_evaluate(rows)
    mismatch = next(({'block': row['name'], 'pyspec': want, 'lean': got}
                     for row, want, got in zip(rows, expected, actual, strict=True)
                     if want != got), None)
    field('ConcreteFFG.state_transition.retained_projection',
          mismatch is None and len(rows) == 48, len(rows), mismatch)
    control = epoch_registry_change(spec, run)
    control_rows, control_expected = retained_projection_rows(
        spec, run, {control['root']: (control['pre'], control['post'])})
    control_index = next(i for i, row in enumerate(control_rows)
                         if row['name'] == f"accepted_slot_{control['slot']}")
    control_actual = differential.lean_evaluate([control_rows[control_index]])[0]
    expected_value = control_expected[control_index]['value']
    actual_value = control_actual.get('value', {})
    detected = (control_actual.get('ok') is True and
                control_actual != control_expected[control_index] and
                actual_value.get('validators') != expected_value['validators'])
    field('ConcreteFFG.state_transition.epoch_registry_change_detected',
          control['after'] != control['before'] and detected, 1,
          None if detected else {'slot': control['slot'], 'expected': control_expected[control_index],
                                 'lean': control_actual})
    for row in projection.check_run(run, projection.source_statements()):
        results.append({'field': row['field'], 'status': row['status'],
                        'checks': 1, 'first_failure': row['state'] if row['status'] == 'FAIL' else None})
    expected_failures = {'ByzantineWeightPremises.estimate_sound',
                         'ByzantineWeightPremises.estimate_sound.uniform_cross_boundary'}
    split = {name: {kind: {'checks': spans[kind]['checks'],
                           'failures': len(spans[kind]['failures'])}
                    for kind in spans}
             for name, spans in (('mixed', mixed), ('uniform', uniform))}
    failure_rows = {name: {kind: spans[kind]['failures'] for kind in spans}
                    for name, spans in (('mixed', mixed), ('uniform', uniform))}
    failure_fingerprint = hashlib.sha256(json.dumps(
        failure_rows, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    if failure_fingerprint != EXPECTED_ESTIMATE_FAILURE_FINGERPRINT:
        raise RuntimeError(f'estimate counterexample set changed: {failure_fingerprint}')
    actual_failures = {row['field'] for row in results if row['status'] == 'FAIL'}
    summary = {'run': run.name, 'validators': len(registry), 'balances_gwei': sorted(set(
                   int(v.effective_balance) for v in registry)),
               'blocks': len(run.roots), 'max_slot': int(tail.slot),
               'fields': len(results), 'failures': sorted(actual_failures),
               'estimate_violations': len(estimate_failures),
               'estimate_split': split,
               'estimate_failure_fingerprint': failure_fingerprint,
               'not_established': sorted(row['field'] for row in results if row['status'] == 'NOT_ESTABLISHED'),
               'results': results,
               'limits': ['single accepted chain and one honest view; network relay, multi-view vote behavior, BLS, engine and KZG are not evaluated',
                          'span_fraction passes vacuously because this fixture has no Byzantine validators']}
    args.output.write_text(json.dumps(summary, indent=2) + '\n')
    print(f'whole-bundle sample: {len(results)} fields; failures={sorted(actual_failures)}; '
          f'estimate violations={len(estimate_failures)}; estimate within/cross: '
          f'mixed {split["mixed"]["within_epoch"]["failures"]}/{split["mixed"]["cross_boundary"]["failures"]}, '
          f'uniform {split["uniform"]["within_epoch"]["failures"]}/{split["uniform"]["cross_boundary"]["failures"]}; '
          f'NOT_ESTABLISHED={summary["not_established"]}')
    if actual_failures != expected_failures:
        print(f'unexpected field result: expected {sorted(expected_failures)}, got {sorted(actual_failures)}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
