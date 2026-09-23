"""Test the payload-branch gap with the unchanged pinned FCR source.

Two bounded runs share the same projected source store and skipped-slot votes.
The first injects child votes which are valid for the source handlers but do
not follow the signing-time head. FCR confirms the child, then two late votes
switch the parent to the opposite payload branch. The second run makes those
voters follow the actual source head; it never confirms the child.

This distinguishes a local store/threshold gap from an honest-history safety
counterexample. The first run violates the honest head-voting condition. It
does not establish a full accepted execution or refute the public theorem.
State transitions, committee queries, signatures, data, and execution checks
use the explicit projection boundary from gloas_payload_delivery_obstacle.py.
All known payloads are verified from the child's insertion onward. The first
skipped-slot EMPTY votes precede the anchor envelope; they are accepted later.
No selected source function body or Python spec file is changed.
The fixture has 3200 validators with balance U = 1_000_000_000 Gwei each.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from gloas_full_instance_obstacle import GloasNode, PIN
from gloas_payload_delivery_obstacle import (
    UNIT,
    Record,
    attestation,
    block,
    initial_store,
    load_source,
)


def projected_source(repo: Path) -> dict:
    spec = load_source(repo)

    def verify_envelope(state, signed_envelope, execution_engine):
        envelope = signed_envelope.message
        assert (envelope.beacon_block_root, state.slot) in [(1, 0), (2, 4)]
        assert state.identity == 100 + envelope.beacon_block_root
        assert envelope.identity == 10000 + envelope.beacon_block_root
        assert envelope.parent_beacon_block_root == (
            0 if envelope.beacon_block_root == 1 else 1
        )

    # These are external data/engine observations, not fork-choice overrides.
    spec["is_data_available"] = lambda root: root in (1, 2)
    spec["verify_execution_payload_envelope"] = verify_envelope
    return spec


def deliver_payload(spec: dict, store: Record, root: int, parent: int) -> None:
    spec["on_execution_payload_envelope"](
        store,
        Record(message=Record(
            beacon_block_root=root,
            parent_beacon_block_root=parent,
            identity=10000 + root,
        )),
    )


def run(spec: dict, inject_child_votes: bool) -> dict:
    store = initial_store(spec)
    fcr = spec["get_fast_confirmation_store"](store)

    # The slot-1 honest voters see the anchor's EMPTY node before its envelope.
    # One slot-1 validator (100) is a separate FULL-vote input. The 299 EMPTY
    # votes below all match this store's head at their signing slots.
    spec["on_tick"](store, 12)
    spec["on_fast_confirmation"](fcr)
    for slot in range(1, 4):
        assert spec["get_head"](store) == GloasNode(1, 0)
        empty_vote = attestation(slot, 1, 0)
        if slot == 1:
            empty_vote.attesting_indices = empty_vote.attesting_indices[1:]
        spec["on_tick"](store, (slot + 1) * 12)
        if slot == 1:
            deliver_payload(spec, store, 1, 0)
            full_vote = attestation(slot, 1, 1)
            full_vote.attesting_indices = [100]
            spec["on_attestation"](store, full_vote)
        spec["on_attestation"](store, empty_vote)
        if slot < 3:
            spec["on_fast_confirmation"](fcr)

    # The child selects FULL after three skipped slots. Its timely proposer
    # boost cannot overcome the historical EMPTY-parent votes.
    child = block(2, 4)
    child.body.signed_execution_payload_bid.message.parent_block_hash = 1001
    spec["on_block"](store, Record(message=child))
    deliver_payload(spec, store, 2, 1)
    birth_head = spec["get_head"](store)
    birth_weights = tuple(
        spec["get_weight"](store, GloasNode(1, status)) for status in (1, 0)
    )
    assert birth_head == GloasNode(1, 0)
    assert all(spec["is_payload_verified"](store, root) for root in store.blocks)
    spec["on_fast_confirmation"](fcr)

    signing_heads = []
    for slot in range(4, 7):
        head = spec["get_head"](store)
        signing_heads.append(head)
        if inject_child_votes:
            # This deliberate input does NOT satisfy honest head voting.
            root, index = 2, int(slot > 4)
        else:
            root = head.root
            index = int(store.blocks[root].slot < slot and head.payload_status == 1)
        vote = attestation(slot, root, index)
        if slot == 6:
            # Two slot-6 validators withhold their votes until after the query.
            vote.attesting_indices = vote.attesting_indices[:-2]
        spec["on_tick"](store, (slot + 1) * 12)
        spec["on_attestation"](store, vote)
        spec["on_fast_confirmation"](fcr)

    assert signing_heads == [GloasNode(1, 0)] * 3
    balance = store.checkpoint_states[store.justified_checkpoint]
    before = spec["get_head"](store)
    confirmed = fcr.confirmed_root
    support = spec["get_attestation_score"](store, spec["get_node_for_root"](2), balance)
    discount = spec["get_support_discount"](store, balance, 2)
    threshold = spec["compute_safety_threshold"](store, 2, balance)
    before_weights = tuple(
        spec["get_weight"](store, GloasNode(1, status)) for status in (1, 0)
    )

    late = attestation(6, 1, 0)
    late.attesting_indices = [698, 699]
    spec["on_attestation"](store, late)
    after = spec["get_head"](store)
    # This query can run again in the same slot. The variable-update handler
    # above was called only once per slot, as the source requires.
    next_confirmed = spec["get_latest_confirmed"](fcr)
    assert all(spec["is_payload_verified"](store, root) for root in store.blocks)
    return dict(
        birth_head=birth_head,
        birth_weights=birth_weights,
        signing_heads=signing_heads,
        before=before,
        confirmed=confirmed,
        support=support,
        discount=discount,
        threshold=threshold,
        before_weights=before_weights,
        after=after,
        next_confirmed=next_confirmed,
    )


def check(repo: Path) -> None:
    spec = projected_source(repo)
    candidate = run(spec, inject_child_votes=True)
    assert candidate["before"] == GloasNode(2, 1)
    assert candidate["confirmed"] == 2
    assert candidate["support"] == 298 * UNIT
    assert candidate["discount"] == 225 * UNIT
    assert candidate["threshold"] == 282 * UNIT + UNIT // 2
    assert candidate["before_weights"] == (299 * UNIT, 299 * UNIT)
    assert candidate["birth_weights"] == (41 * UNIT, 299 * UNIT)
    assert candidate["after"] == GloasNode(1, 0)
    assert candidate["next_confirmed"] == 1

    control = run(spec, inject_child_votes=False)
    assert control["before"] == GloasNode(1, 0)
    assert control["confirmed"] == 1
    assert control["support"] == 0
    assert control["after"] == GloasNode(1, 0)
    assert control["next_confirmed"] == 1

    print(f"pin={PIN}")
    print("projection: slot=7 support=298U discount=225U threshold=282.5U")
    print(f"projection: before={candidate['before']} confirmed={candidate['confirmed']}")
    print(f"projection: after_two_late_votes={candidate['after']} "
          f"next_confirmed={candidate['next_confirmed']}")
    print(f"history_gap: birth_head={candidate['birth_head']} "
          f"signing_heads={candidate['signing_heads']}")
    print(f"head_following_control: head={control['before']} "
          f"confirmed={control['confirmed']} child_support=0")
    print("SCOPE: exact source projection; child-vote run violates honest head voting")
    print("RESULT: local FCR threshold gap reproduced; no accepted safety counterexample")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--consensus-repo", type=Path, required=True)
    check(parser.parse_args().consensus_repo)


if __name__ == "__main__":
    main()
