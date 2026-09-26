#!/usr/bin/env python3
"""Realized/unrealized justification gap: semantic regression on real runs.

The test drives the pinned Gloas pyspec fork choice through three runs and
projects each run onto `AcceptedBlockFFGState`:

* evidence: a checkpoint is available at a root when votes in attestations
  included in the block bodies on that root's chain certify it from the
  anchor (`IncludedCertifiedJustified`), and its root is on that chain;
* selectors: `realized_*` read the block state, `unrealized_*` read
  `process_justification_and_finalization` on the block state, and a
  `GENESIS_EPOCH` read (the genesis stub) reads as the anchor.

The runs are:

* `full`: every slot has a block that includes the previous slot's votes.
  The slot-16 block has realized justification epoch 0 and unrealized
  justification epoch 1, with the epoch-1 certificate included in epoch 1.
* `late`: epoch-2 votes are included in epoch 3 and epoch-3 votes in
  epoch 4. The boundary at the end of epoch 4 finalizes epoch 2 through the
  2-step link 2 -> 4; no 1-step link 2 -> 3 exists.
* `fork`: blocks at slots 1-15 and no block on that chain in epoch 2. A
  block at slot 16 on the slot-8 block includes the epoch-1 votes. The
  Python fast confirmation rule confirms the slot-15 block, and the head
  leaves it at slot 24.

Names `AcceptedBlockFFGState.*` and `FFGStateReadAgreement.*` are Lean
fields; `semantics.*` is a Python fact that Lean does not state; `candidate.*`
is a proposed restatement; `regression.*` records a finding.

Each law is checked on every applicable tuple. A law marked `expected=FAIL`
is a labelled regression: the test fails if it stops failing, because the
run then no longer reproduces the finding.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_contracts as tc  # noqa: E402

GENESIS_EPOCH = 0


class Run:
    """A fork-choice store driven by explicit blocks and votes."""

    def __init__(self, env, name):
        self.env = env
        self.name = name
        spec = env["spec"]
        st = env["genesis"](spec, [32 * 10**9] * 64, 32 * 10**9)
        block = spec.BeaconBlock(slot=st.slot)
        st.latest_block_header.body_root = spec.hash_tree_root(block.body)
        block.state_root = spec.hash_tree_root(st)
        self.store = spec.get_forkchoice_store(st.copy(), block)
        self.anchor_root = spec.hash_tree_root(block)
        self.anchor = (0, bytes(self.anchor_root).hex())
        self.messages = {self.anchor_root: block}
        self.pool = {}
        self.delivered = set()
        self.fcr = None
        self.confirmed = {}

    def tick(self, slot):
        spec = self.env["spec"]
        time_ = int(self.store.genesis_time) + slot * spec.config.SLOT_DURATION_MS // 1000
        if time_ > int(self.store.time):
            spec.on_tick(self.store, time_)
        # Gossip delivery of earlier votes. It also stores the target
        # checkpoint states that `get_head` reads.
        for s in sorted(self.pool):
            if s < slot and s not in self.delivered:
                self.delivered.add(s)
                try:
                    spec.on_attestation(self.store, self.pool[s], is_from_block=False)
                except AssertionError:
                    pass

    def vote(self, slot, head):
        """The aggregate of all committees at `slot` for `head`."""
        spec = self.env["spec"]
        st = self.store.block_states[head].copy()
        if int(st.slot) < slot:
            spec.process_slots(st, slot)
        self.pool[slot] = self.env["attest"](st, spec, slot, beacon_block_root=head)
        return self.pool[slot]

    def propose(self, slot, parent, vote_slots):
        spec = self.env["spec"]
        pre = self.store.block_states[parent].copy()
        block = self.env["build_block"](spec, pre, slot=slot)
        for s in vote_slots:
            block.body.attestations.append(self.pool[s])
        signed = self.env["sign_transition"](spec, pre, block)
        self.tick(slot)
        spec.on_block(self.store, signed)
        root = spec.hash_tree_root(signed.message)
        self.messages[root] = signed.message
        return root

    def confirm(self):
        spec = self.env["spec"]
        if self.fcr is None:
            self.fcr = spec.get_fast_confirmation_store(self.store)
        spec.store_target_checkpoint_state(self.store, self.store.justified_checkpoint)
        spec.on_fast_confirmation(self.fcr)
        self.confirmed[int(spec.get_current_slot(self.store))] = self.fcr.confirmed_root


def full_run(env, last_slot=40):
    run = Run(env, "full")
    parent = run.anchor_root
    for slot in range(1, last_slot + 1):
        parent = run.propose(slot, parent, [slot - 1] if slot >= 2 else [])
        run.vote(slot, parent)
    return run


def late_run(env):
    run = Run(env, "late")
    parent = run.anchor_root
    for slot in range(1, 45):
        epoch = slot // 8
        if slot == 24:
            votes = list(range(16, 24))
        elif slot == 32:
            votes = list(range(24, 32))
        elif slot >= 2 and (slot - 1) // 8 not in (2, 3):
            votes = [slot - 1]
        else:
            votes = []
        parent = run.propose(slot, parent, votes)
        run.vote(slot, parent)
        assert epoch == slot // 8
    return run


def fork_run(env):
    spec = env["spec"]
    run = Run(env, "fork")
    parent = run.anchor_root
    roots = {0: run.anchor_root}
    for slot in range(1, 26):
        run.tick(slot)
        run.confirm()
        if slot <= 15:
            parent = run.propose(slot, parent, [slot - 1] if slot >= 2 else [])
            roots[slot] = parent
        elif slot == 16:
            run.x = run.propose(16, roots[8], list(range(8, 16)))
        head = spec.get_head(run.store).root
        run.vote(slot, head)
    run.seed = roots[15]
    run.base = roots[8]
    return run


class Projection:
    """`AcceptedBlockFFGState` read off one run."""

    def __init__(self, run):
        self.run = run
        spec = run.env["spec"]
        store = run.store
        self.spec = spec
        self.roots = list(store.blocks)
        self.slot = {r: int(store.blocks[r].slot) for r in self.roots}
        self.epoch = {r: self.slot[r] // int(spec.SLOTS_PER_EPOCH) for r in self.roots}
        self.parent = {r: store.blocks[r].parent_root for r in self.roots}
        self.chain = {}
        for r in self.roots:
            chain, x = [], r
            while x in store.blocks:
                chain.append(x)
                if x == run.anchor_root:
                    break
                x = self.parent[x]
            self.chain[r] = chain
        self.total = int(spec.get_total_active_balance(store.block_states[run.anchor_root]))
        self.balance = [int(v.effective_balance) for v in store.block_states[run.anchor_root].validators]
        self.gj, self.gf, self.gu, self.guf, self.stored_gu = {}, {}, {}, {}, {}
        for r in self.roots:
            st = store.block_states[r]
            eager = st.copy()
            spec.process_justification_and_finalization(eager)
            self.gj[r] = self.read(st.current_justified_checkpoint)
            self.gf[r] = self.read(st.finalized_checkpoint)
            self.gu[r] = self.read(eager.current_justified_checkpoint)
            self.guf[r] = self.read(eager.finalized_checkpoint)
            self.stored_gu[r] = self.read(store.unrealized_justifications[r])
        self.links = {r: self.included_links(r) for r in self.roots}
        self.certified = {r: self.certify(r) for r in self.roots}

    def read(self, c):
        """`CheckpointReadsAs`: a `GENESIS_EPOCH` read is the anchor."""
        raw = tc.cp(c)
        return self.run.anchor if raw[0] == GENESIS_EPOCH else raw

    def included_links(self, r):
        """Signers of each (source, target) pair over the included votes."""
        spec, store = self.spec, self.run.store
        links = {}
        for carrier in self.chain[r]:
            state = store.block_states[carrier]
            for a in self.run.messages[carrier].body.attestations:
                key = (self.read(a.data.source), tc.cp(a.data.target))
                links.setdefault(key, set()).update(int(i) for i in spec.get_attesting_indices(state, a))
        return links

    def supermajority(self, signers):
        return 2 * self.total <= 3 * sum(self.balance[i] for i in signers)

    def on_chain(self, r, root_hex):
        return any(bytes(x).hex() == root_hex for x in self.chain[r])

    def link(self, r, source, target):
        return self.supermajority(self.links[r].get((source, target), set()))

    def certify(self, r):
        """`IncludedCertifiedJustified` from the anchor, restricted to
        checkpoints whose root is on `r`'s chain."""
        done = {self.run.anchor}
        grew = True
        while grew:
            grew = False
            for (source, target), signers in self.links[r].items():
                if (source in done and target not in done and source[0] < target[0]
                        and self.on_chain(r, target[1]) and self.supermajority(signers)):
                    done.add(target)
                    grew = True
        return done

    def AU(self, r):
        return self.certified[r]

    def finalized_one_step(self, r, c):
        """`IncludedCertifiedFinalized`: justified, and a link to epoch + 1."""
        return c in self.certified[r] and any(
            s == c and t[0] == c[0] + 1 and self.supermajority(sig)
            for (s, t), sig in self.links[r].items())

    def finalized_k_step(self, r, c):
        """Candidate: a link to epoch + 1 or + 2, with the skipped epoch
        justified on the chain (the PJF rules 1 and 3)."""
        if c not in self.certified[r]:
            return False
        for (s, t), sig in self.links[r].items():
            if s != c or not self.supermajority(sig):
                continue
            if t[0] == c[0] + 1:
                return True
            if t[0] == c[0] + 2 and any(x[0] == c[0] + 1 for x in self.certified[r]):
                return True
        return False


def run_checks(projections, fork):
    results = []

    def check(name, statement, cases, predicate, expected="PASS"):
        errors, crashes, count = [], [], 0
        for label, data in cases:
            count += 1
            try:
                ok, fields = predicate(data)
            except Exception as exc:  # a crash is never an expected result
                crashes.append({"case": label, "exception": f"{type(exc).__name__}: {exc}"})
                continue
            if not ok:
                errors.append({"case": label, **fields})
        status = "ERROR" if crashes or not count else "FAIL" if errors else "PASS"
        errors = crashes + errors
        results.append({"law": name, "statement": statement, "status": status,
                        "expected": expected, "cases": count, "counterexamples": errors[:4]})
        mark = "" if status == expected else "  <-- UNEXPECTED"
        print(f"{status} {name} ({count} cases; expected {expected}){mark}", flush=True)

    def roots(pred=lambda P, r: True):
        return [(f"{P.run.name}:{P.slot[r]}", (P, r)) for P in projections for r in P.roots if pred(P, r)]

    def seeds(pred):
        out = []
        for P in projections:
            for r in P.roots:
                for seed in P.chain[r]:
                    if pred(P, r, seed):
                        for c in sorted(P.AU(seed)):
                            out.append((f"{P.run.name}:{P.slot[r]}<-{P.slot[seed]}:{c[0]}", (P, r, seed, c)))
        return out

    def at_root(pred):
        return [(f"{P.run.name}:{P.slot[r]}:{c[0]}", (P, r, c))
                for P in projections for r in P.roots if pred(P, r) for c in sorted(P.AU(r))]

    block = lambda P, r: r != P.run.anchor_root  # noqa: E731

    def realized_fields(d):
        P, r, seed, c = d
        return c[0] <= P.gj[r][0], {"block_epoch": P.epoch[r], "seed_epoch": P.epoch[seed],
                                    "checkpoint": c, "realized_justified": P.gj[r]}

    check("AcceptedBlockFFGState.realized_justified_max",
          "BlockKnown r b -> BlockKnown seed sb -> RootDescends r seed -> epoch sb < epoch b -> "
          "GENESIS_EPOCH + 2 < epoch b -> AvailableCheckpoint seed c -> c.epoch <= (realized_justified r).epoch",
          seeds(lambda P, r, s: block(P, r) and P.epoch[s] < P.epoch[r] and GENESIS_EPOCH + 2 < P.epoch[r]),
          realized_fields)
    check("regression.realized_justified_max_before_restatement",
          "Old form: BlockKnown r b -> AvailableCheckpoint r c -> c.epoch < epoch b -> "
          "c.epoch <= (realized_justified r).epoch (slot-16 block of `full`; slot-32 block of `late`)",
          seeds(lambda P, r, s: block(P, r) and s == r),
          lambda d: (d[3][0] >= d[0].epoch[d[1]] or d[3][0] <= d[0].gj[d[1]][0],
                     realized_fields(d)[1]), expected="FAIL")
    check("regression.realized_justified_max_seed_in_epoch_one",
          "The early-return boundary: seed and block epochs 1 < 2 are not enough; "
          "the slot-16 block with the slot-15 seed has realized epoch 0",
          seeds(lambda P, r, s: block(P, r) and P.epoch[s] < P.epoch[r] and P.epoch[r] == GENESIS_EPOCH + 2),
          realized_fields, expected="FAIL")

    def unrealized_fields(d):
        P, r, c = d
        return c[0] <= P.gu[r][0], {"block_epoch": P.epoch[r], "checkpoint": c, "unrealized_justified": P.gu[r]}

    check("AcceptedBlockFFGState.unrealized_justified_max",
          "BlockKnown r b -> GENESIS_EPOCH + 1 < epoch b -> AvailableCheckpoint r c -> "
          "c.epoch <= (unrealized_justified r).epoch",
          at_root(lambda P, r: block(P, r) and GENESIS_EPOCH + 1 < P.epoch[r]), unrealized_fields)
    check("regression.unrealized_justified_max_before_restatement",
          "Old form without the epoch bound: AvailableCheckpoint r c -> c.epoch <= (unrealized_justified r).epoch "
          "(the epoch-1 blocks after slot 8)",
          at_root(lambda P, r: True), unrealized_fields, expected="FAIL")
    check("AcceptedBlockFFGState.realized_justified_realized",
          "BlockKnown r b -> realized_justified r = anchor or exists seed sb, RootDescends r seed and "
          "BlockKnown seed sb and epoch sb < epoch b and GENESIS_EPOCH + 2 < epoch b and "
          "AvailableCheckpoint seed (realized_justified r)",
          roots(block),
          lambda d: (d[0].gj[d[1]] == d[0].run.anchor or (
                         GENESIS_EPOCH + 2 < d[0].epoch[d[1]] and
                         any(d[0].epoch[s] < d[0].epoch[d[1]] and d[0].gj[d[1]] in d[0].AU(s)
                             for s in d[0].chain[d[1]])),
                     {"gj": d[0].gj[d[1]], "block_epoch": d[0].epoch[d[1]]}))
    check("AcceptedBlockFFGState.realized_justified_epoch_le_unrealized",
          "(realized_justified r).epoch <= (unrealized_justified r).epoch",
          roots(), lambda d: (d[0].gj[d[1]][0] <= d[0].gu[d[1]][0], {"gj": d[0].gj[d[1]], "gu": d[0].gu[d[1]]}))

    def descents(pred):
        return [(f"{P.run.name}:{P.slot[r]}<-{P.slot[s]}", (P, r, s))
                for P in projections for r in P.roots for s in P.chain[r] if pred(P, r, s)]

    check("AcceptedBlockFFGState.unrealized_justified_mono",
          "RootDescends tip seed -> (unrealized_justified seed).epoch <= (unrealized_justified tip).epoch",
          descents(lambda P, r, s: True),
          lambda d: (d[0].gu[d[2]][0] <= d[0].gu[d[1]][0], {"gu_seed": d[0].gu[d[2]], "gu_tip": d[0].gu[d[1]]}))
    check("AcceptedBlockFFGState.unrealized_justified_epoch_le_later_realized",
          "BlockKnown seed sb -> BlockKnown tip tb -> RootDescends tip seed -> epoch sb < epoch tb -> "
          "(unrealized_justified seed).epoch <= (realized_justified tip).epoch",
          descents(lambda P, r, s: P.epoch[s] < P.epoch[r]),
          lambda d: (d[0].gu[d[2]][0] <= d[0].gj[d[1]][0], {"gu_seed": d[0].gu[d[2]], "gj_tip": d[0].gj[d[1]],
                                                          "seed_epoch": d[0].epoch[d[2]], "tip_epoch": d[0].epoch[d[1]]}))
    check("semantics.unrealized_justified_early",
          "BlockKnown r b -> epoch b <= GENESIS_EPOCH + 1 -> unrealized_justified r = realized_justified r",
          roots(lambda P, r: P.epoch[r] <= GENESIS_EPOCH + 1),
          lambda d: (d[0].gu[d[1]] == d[0].gj[d[1]], {"gu": d[0].gu[d[1]], "gj": d[0].gj[d[1]]}))
    check("AcceptedBlockFFGState.unrealized_finalized_epoch_le_realized_justified",
          "(unrealized_finalized r).epoch <= (realized_justified r).epoch",
          roots(), lambda d: (d[0].guf[d[1]][0] <= d[0].gj[d[1]][0], {"guf": d[0].guf[d[1]], "gj": d[0].gj[d[1]]}))
    check("AcceptedBlockFFGState.available_checkpoint_epoch_le_block",
          "BlockKnown r b -> AvailableCheckpoint r c -> c.epoch <= epoch b",
          at_root(block), lambda d: (d[2][0] <= d[0].epoch[d[1]], {"checkpoint": d[2], "block_epoch": d[0].epoch[d[1]]}))
    check("AcceptedBlockFFGState.realized_justified_anchor_or_before",
          "realized_justified r = anchor or (realized_justified r).epoch < epoch b",
          roots(block), lambda d: (d[0].gj[d[1]] == d[0].run.anchor or d[0].gj[d[1]][0] < d[0].epoch[d[1]],
                                   {"gj": d[0].gj[d[1]], "block_epoch": d[0].epoch[d[1]]}))
    for field, sel in (("realized_justified", "gj"), ("unrealized_justified", "gu"),
                       ("realized_finalized", "gf"), ("unrealized_finalized", "guf")):
        check(f"AcceptedBlockFFGState.{field}_mem",
              f"AvailableCheckpoint r ({field} r)",
              roots(), lambda d, sel=sel: (getattr(d[0], sel)[d[1]] in d[0].AU(d[1]),
                                           {"selector": getattr(d[0], sel)[d[1]], "available": sorted(d[0].AU(d[1]))}))
    check("AcceptedBlockFFGState.realized_finalized_epoch_le_realized_justified",
          "(realized_finalized r).epoch <= (realized_justified r).epoch",
          roots(), lambda d: (d[0].gf[d[1]][0] <= d[0].gj[d[1]][0], {"gf": d[0].gf[d[1]], "gj": d[0].gj[d[1]]}))
    check("AcceptedBlockFFGState.unrealized_finalized_epoch_le_unrealized_justified",
          "(unrealized_finalized r).epoch <= (unrealized_justified r).epoch",
          roots(), lambda d: (d[0].guf[d[1]][0] <= d[0].gu[d[1]][0], {"guf": d[0].guf[d[1]], "gu": d[0].gu[d[1]]}))
    check("FFGStateReadAgreement.transition_gu",
          "store.unrealized_justifications r reads as unrealized_justified r",
          roots(), lambda d: (d[0].stored_gu[d[1]] == d[0].gu[d[1]], {"stored": d[0].stored_gu[d[1]], "eager": d[0].gu[d[1]]}))
    for field, sel in (("realized_finalized_evidence", "gf"), ("unrealized_finalized_evidence", "guf")):
        check(f"regression.{field}_one_step",
              f"{field}: {field.rsplit('_', 1)[0]} r = anchor or IncludedCertifiedFinalized (1-step link) "
              "(`late`: epoch 2 is finalized through the link 2 -> 4)",
              roots(), lambda d, sel=sel: (getattr(d[0], sel)[d[1]] == d[0].run.anchor
                                           or d[0].finalized_one_step(d[1], getattr(d[0], sel)[d[1]]),
                                           {"finalized": getattr(d[0], sel)[d[1]]}), expected="FAIL")
        check(f"candidate.{field}_two_step",
              f"{field.rsplit('_', 1)[0]} r = anchor or (justified, a link to epoch + 1, or a link to "
              "epoch + 2 with epoch + 1 justified), all on r's chain",
              roots(), lambda d, sel=sel: (getattr(d[0], sel)[d[1]] == d[0].run.anchor
                                           or d[0].finalized_k_step(d[1], getattr(d[0], sel)[d[1]]),
                                           {"finalized": getattr(d[0], sel)[d[1]]}))

    # Slot-16 witness of the gap in `full`.
    full = projections[0]
    s16 = [r for r in full.roots if full.slot[r] == 16]
    check("regression.slot16_gap",
          "The slot-16 block of `full`: realized epoch 0, unrealized epoch 1, and epoch 1 available at slot 15",
          [("full:16", s16[0])],
          lambda r: (full.gj[r][0] == 0 and full.gu[r][0] == 1
                     and any(c[0] == 1 for c in full.AU(full.parent[r])),
                     {"gj": full.gj[r], "gu": full.gu[r], "parent_available": sorted(full.AU(full.parent[r]))}))

    # A3.2 at e = 1 on `fork`.
    P = fork
    spec = P.spec
    store = P.run.store
    base_cp = tc.cp(spec.get_checkpoint_for_block(store, P.run.base, spec.Epoch(1)))
    a32 = [(f"fork:{P.slot[r]}", r) for r in P.roots
           if base_cp in P.AU(r) and P.run.base in P.chain[r] and P.epoch[r] < 1 + 2]
    check("regression.a32_projection_epoch_one_seed",
          "Old step: AvailableCheckpoint seed (C b 1) -> epoch seed < 3 -> 1 <= GU(seed).epoch "
          "(the slot-15 seed has GU epoch 0)",
          a32, lambda r: (1 <= P.gu[r][0], {"seed_epoch": P.epoch[r], "gu": P.gu[r]}), expected="FAIL")
    check("candidate.a32_projection_seed_after_epoch_one",
          "AvailableCheckpoint seed (C b 1) -> GENESIS_EPOCH + 1 < epoch seed -> 1 <= GU(seed).epoch",
          [(l, r) for l, r in a32 if P.epoch[r] > GENESIS_EPOCH + 1],
          lambda r: (1 <= P.gu[r][0], {"seed_epoch": P.epoch[r], "gu": P.gu[r]}))
    seed_confirmed = [s for s, root in P.run.confirmed.items() if root == P.run.seed]
    head = spec.get_head(store).root
    check("regression.fcr_confirmed_block_reorged_epoch_one",
          "The Python FCR confirms the slot-15 block; at slot 25 the head does not descend from it",
          [("fork:25", head)],
          lambda h: (not seed_confirmed or spec.is_ancestor(store, spec.get_node_for_root(h),
                                                            spec.get_node_for_root(P.run.seed)),
                     {"confirmed_at_slots": seed_confirmed, "head_slot": P.slot[h],
                      "head_is_fork_block": h == P.run.x}), expected="FAIL")
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    start = time.monotonic()
    (spec, _phase0, genesis, _with_attestations, build_block, sign_transition,
     _get_attestation, _attester_slashing, _proposer_slashing) = tc.setup(args.repo)
    from eth_consensus_specs.test.helpers.attestations import get_valid_attestation_at_slot
    env = {"spec": spec, "genesis": genesis, "build_block": build_block,
           "sign_transition": sign_transition, "attest": get_valid_attestation_at_slot}
    projections = [Projection(full_run(env)), Projection(late_run(env)), Projection(fork_run(env))]
    results = run_checks(projections, projections[2])
    unexpected = [r for r in results if r["status"] != r["expected"]]
    elapsed = round(time.monotonic() - start, 3)
    if args.output:
        args.output.write_text(json.dumps({"pin": tc.PIN, "runtime_seconds": elapsed,
                                           "results": results}, indent=2, default=str) + "\n")
    print(f"realized gap: {len(results)} laws; {len(unexpected)} unexpected; {elapsed} s", flush=True)
    return bool(unexpected)


if __name__ == "__main__":
    raise SystemExit(main())
