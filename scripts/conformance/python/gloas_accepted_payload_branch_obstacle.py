"""Two honest views expose the Gloas payload-branch safety obstruction.

Execute unchanged fork-choice and FCR function bodies from the pinned source.
The explicit external projection matches the Lean model: fixed committees and
registry, projected state transitions, a fixed signed-data validity table, and
valid envelope observations. Every honest vote is its signing-time head vote
and is delivered as a singleton to both views at the next slot boundary. All
payloads satisfy the authorized end-of-slot relay field. Byzantine validators
send conflicting payload-status votes to the two views; neither view receives
both versions, and no slashing event occurs.

At slot 11 the source FCR confirms child 2. At slot 12 the honest target head
is anchor 1 EMPTY, so it excludes child 2 although both envelopes are verified.
This is an exact-source execution at the model external boundary. It is not a
full generated-pyspec state transition trace or a kernel proof of every public
accepted-theorem assumption record. No selected source function body changes.
"""
from __future__ import annotations

import argparse
from pathlib import Path
from types import MappingProxyType

from gloas_full_instance_obstacle import Checkpoint, GloasNode, PIN
from gloas_payload_delivery_obstacle import (
    UNIT, Record, attestation, block, initial_store, load_source,
)


def check(repo: Path) -> None:
    """Run the two-view confirmed-child execution, with no altered source body."""
    spec = load_source(repo)
    signed_honest = {}
    all_validators = set(range(3200))
    byzantine = {slot * 100 + i for slot in range(1, 32) for i in range(25)}
    honest = all_validators - byzantine
    target_cohort = {0} | {slot * 100 + i for slot in range(1, 7) for i in range(50, 100)}
    source_cohort = honest - target_cohort
    assert source_cohort and target_cohort

    def data_key(data):
        return (data.slot, data.index, data.beacon_block_root, data.source, data.target)

    # Fix the signature relation before the execution starts. The live signing
    # checks below must reproduce this exact table by running honest fork choice.
    signed_registry = MappingProxyType({
        (validator, validator // 100): data_key(attestation(
            validator // 100,
            1 if validator // 100 < 7 else 2,
            (int(validator in source_cohort) if 1 <= validator // 100 < 7
             else int(validator // 100 > 7)),
        ).data)
        for validator in honest
    })

    def validity(state, vote):
        indices = vote.attesting_indices
        slot = vote.data.slot
        return (len(state.validators) == 3200 and bool(indices)
            and indices == sorted(set(indices))
            and all(slot * 100 <= i < (slot + 1) * 100 for i in indices)
            and all(i not in honest or signed_registry.get((i, slot)) == data_key(vote.data)
                    for i in indices))

    def process_slots(state, slot):
        # Total completion of the Lean external: unused non-advancing inputs
        # preserve the state, while every advancing input lands on its slot.
        if state.slot < slot:
            state.slot = slot

    def process_justification_and_finalization(state):
        # The reachable states retain anchor checkpoints. This completion also
        # satisfies the global no-future-checkpoint law on malformed inputs.
        for field in ("current_justified_checkpoint", "finalized_checkpoint"):
            if getattr(state, field).epoch > state.slot // 32:
                setattr(state, field, Checkpoint(0, 1))

    def transition(state, signed_block, validate_result=True):
        # Other inputs reject (the Lean Option result is none). Only the fixed
        # child of the committed anchor is in this execution's external graph.
        child = signed_block.message
        assert validate_result and state.slot == 0 < child.slot == 7
        assert state.identity == 101 and len(state.validators) == 3200
        assert (child.root, child.parent_root) == (2, 1)
        assert state.current_justified_checkpoint == Checkpoint(0, 1)
        assert state.finalized_checkpoint == Checkpoint(0, 1)
        assert child.body.signed_execution_payload_bid.message.parent_block_hash == 1001
        state.slot = 7
        state.identity = 102
        state.current_justified_checkpoint = Checkpoint(0, 1)
        state.finalized_checkpoint = Checkpoint(0, 1)

    def verify_envelope(state, signed_envelope, execution_engine):
        env = signed_envelope.message
        assert (env.beacon_block_root, state.slot) in ((1, 0), (2, 7))
        assert state.identity == 100 + env.beacon_block_root
        assert env.identity == 10000 + env.beacon_block_root
        assert env.parent_beacon_block_root == (0 if env.beacon_block_root == 1 else 1)

    # This is the explicit Lean-model external boundary. Signature validity is
    # confined to committee members and recorded honest data; the empty default
    # state rejects. Slot processing and transition preserve the fixed registry.
    spec.update(is_valid_indexed_attestation=validity, process_slots=process_slots,
        process_justification_and_finalization=process_justification_and_finalization,
        state_transition=transition, verify_execution_payload_envelope=verify_envelope,
        is_data_available=lambda root: root in (1, 2))
    stores = {name: initial_store(spec) for name in ("source", "target")}
    fcr = {name: spec["get_fast_confirmation_store"](store) for name, store in stores.items()}
    accepted = dict(blocks=0, envelopes=0, attestations=0)
    honest_delivered = {name: set() for name in stores}
    observations = []
    ledger_observation = None
    envelope_received = {}
    block_received = {}

    def tick(second):
        for store in stores.values():
            spec["on_tick"](store, second)

    def fast_confirm():
        for name in stores:
            spec["on_fast_confirmation"](fcr[name])

    def envelope(name, root):
        spec["on_execution_payload_envelope"](stores[name], Record(message=Record(
            beacon_block_root=root, parent_beacon_block_root=0 if root == 1 else 1,
            identity=10000 + root)))
        envelope_received[name, root] = int(stores[name].time)
        accepted["envelopes"] += 1

    def vote(slot, indices, name=None, root=None, index=None):
        indices = list(indices)
        if name is not None:
            store = stores[name]
            head = spec["get_head"](store)
            root = head.root
            index = int(store.blocks[root].slot < slot and head.payload_status == 1)
            assert int(store.time) // 12 == slot
            assert set(indices) <= (source_cohort if name == "source" else target_cohort)
        result = attestation(slot, root, index)
        result.attesting_indices = indices
        if name is not None:
            for validator in indices:
                assert (validator, slot) not in signed_honest
                assert signed_registry[validator, slot] == data_key(result.data)
                signed_honest[validator, slot] = data_key(result.data)
        else:
            assert set(indices) <= byzantine
        return result

    def deliver(common, split):
        for name, store in stores.items():
            singletons = [Record(attesting_indices=[i], data=aggregate.data)
                          for aggregate in common for i in aggregate.attesting_indices]
            for att in [*singletons, split[name]]:
                if att is None:
                    continue
                assert int(store.time) == 12 * (att.data.slot + 1)
                # Verify the new relay's pre-validation consequence directly.
                assert att.data.index != 1 or spec["is_payload_verified"](store, att.data.beacon_block_root)
                assert validity(store.checkpoint_states[store.justified_checkpoint], att)
                spec["on_attestation"](store, att)
                accepted["attestations"] += 1
                for i in att.attesting_indices:
                    if i in honest:
                        assert att.attesting_indices == [i]
                        key = (i, int(att.data.slot))
                        assert key not in honest_delivered[name]
                        honest_delivered[name].add(key)

    # Slot zero: source and target have the same committed anchor and EMPTY head.
    common = [vote(0, [0], "target"), vote(0, range(1, 100), "source")]
    split = dict(source=None, target=None)
    tick(12)
    deliver(common, split)
    fast_confirm()

    # Slot 1 bootstrap. EMPTY honest votes precede the target's envelope. The
    # source receives it at second 13; both classes have it by second 23.
    empty = vote(1, range(150, 200), "target")
    tick(13)
    envelope("source", 1)
    full = vote(1, range(125, 150), "source")
    assert (empty.data.index, full.data.index) == (0, 1)
    tick(23)
    envelope("target", 1)
    common = [empty, full]
    split = {name: vote(1, range(100, 125), root=1, index=int(name == "source"))
             for name in stores}

    for slot in range(2, 32):
        tick(slot * 12)
        deliver(common, split)
        fast_confirm()
        for store in stores.values():
            assert spec["is_payload_verified"](store, 1)
        if slot <= 7:
            assert spec["get_head"](stores["source"]) == GloasNode(1, 1)
            assert spec["get_head"](stores["target"]) == GloasNode(1, 0)
        if slot == 7:
            tick(85)
            child = block(2, 7)
            child.body.signed_execution_payload_bid.message.parent_block_hash = 1001
            for name, store in stores.items():
                spec["on_block"](store, Record(message=child))
                accepted["blocks"] += 1
                block_received[name, 2] = 85
                envelope(name, 2)
            assert spec["get_head"](stores["source"]) == GloasNode(2, 1)
            assert spec["get_head"](stores["target"]) == GloasNode(1, 0)
        if slot >= 8:
            source, target = stores["source"], stores["target"]
            balance = source.checkpoint_states[source.justified_checkpoint]
            item = dict(slot=slot, source_confirmed=int(fcr["source"].confirmed_root),
                source_head=spec["get_head"](source).root,
                target_head=spec["get_head"](target).root,
                support=spec["get_attestation_score"](source, spec["get_node_for_root"](2), balance),
                threshold=spec["compute_safety_threshold"](source, 2, balance),
                discount=spec["get_support_discount"](source, balance, 2),
                full=spec["get_weight"](target, GloasNode(1, 1)),
                empty=spec["get_weight"](target, GloasNode(1, 0)))
            observations.append(item)
            if slot == 11:
                assert item == dict(slot=11, source_confirmed=2, source_head=2,
                    target_head=1, support=400*UNIT, threshold=395*UNIT,
                    discount=450*UNIT, full=450*UNIT, empty=550*UNIT), item
            if slot == 12:
                assert fcr["source"].confirmed_root == 2
                assert spec["get_head"](target) == GloasNode(1, 0)
                assert not spec["is_ancestor"](target, spec["get_head"](target), spec["get_node_for_root"](2))
                assert (item["full"], item["empty"]) == (525*UNIT, 575*UNIT)
                window = set(range(100, 1200))  # lo=1 through sigma=11.
                supporters = {i for i in window & honest
                    if signed_registry[i, i // 100][2] == 2}
                ancestor_full = {i for i in window & honest
                    if signed_registry[i, i // 100][2] == 1
                    and signed_registry[i, i // 100][1] == 1}
                ancestor_empty = {i for i in window & honest
                    if signed_registry[i, i // 100][2] == 1
                    and signed_registry[i, i // 100][1] == 0}
                conflicting = (window & honest) - supporters - ancestor_full - ancestor_empty
                byz_window = window & byzantine
                assert all(target.latest_messages[i].root == 2 for i in supporters)
                assert all(target.latest_messages[i].root == 1
                    and not target.latest_messages[i].payload_present for i in byz_window)
                ledger_observation = dict(S=len(supporters)*UNIT,
                    X=len(conflicting)*UNIT, B=len(byz_window)*UNIT,
                    P=spec["get_proposer_score"](target),
                    ancestor_FULL=len(ancestor_full)*UNIT,
                    ancestor_EMPTY=len(ancestor_empty)*UNIT)
                assert ledger_observation == dict(S=375*UNIT, X=0, B=275*UNIT,
                    P=40*UNIT, ancestor_FULL=150*UNIT, ancestor_EMPTY=300*UNIT)
                assert ledger_observation["S"] >= sum(ledger_observation[k]
                    for k in ("X", "B", "P")) + 1
                assert item["full"] == ledger_observation["S"] + ledger_observation["ancestor_FULL"]
                assert item["empty"] == ledger_observation["B"] + ledger_observation["ancestor_EMPTY"]
        if slot < 7:
            common = [vote(slot, range(slot*100+25, slot*100+50), "source"),
                      vote(slot, range(slot*100+50, slot*100+100), "target")]
            split = {name: vote(slot, range(slot*100, slot*100+25), root=1,
                               index=int(name == "source")) for name in stores}
        else:
            common = [vote(slot, range(slot*100+25, slot*100+100), "source")]
            split = dict(source=vote(slot, range(slot*100, slot*100+25), root=2,
                                    index=int(slot > 7)),
                         target=vote(slot, range(slot*100, slot*100+25), root=1, index=0))
    tick(384)
    deliver(common, split)  # Horizon lookahead delivers the last in-horizon votes.
    assert len(signed_honest) == len(honest) == 2425
    assert signed_honest == dict(signed_registry)
    assert all(received == set(signed_registry) for received in honest_delivered.values())
    assert {v for v, slot in signed_honest} == honest
    assert all(len({slot for v, slot in signed_honest if v == i}) == 1 for i in honest)
    # Uniform weights and fixed disjoint committees establish the 25% bound for
    # every interval, as well as the exact same-epoch committee weight estimate.
    for lo in range(32):
        for hi in range(lo, 32):
            participants = set(range(lo*100, (hi+1)*100))
            assert 100 * len(participants & byzantine) <= 25 * len(participants)
            assert spec["estimate_committee_weight_between_slots"](3200*UNIT, lo, hi) >= len(participants)*UNIT
    for root in (1, 2):
        first = min(envelope_received[name, root] for name in stores)
        deadline = (first // 12 + 1) * 12 - 1
        assert all(envelope_received[name, root] <= deadline for name in stores)
    assert block_received["source", 2] == block_received["target", 2]
    print(f"pin={PIN}")
    print("honest_head_votes=2425 byzantine_validators=775 committee_bound=25_percent")
    print(f"accepted_handlers={accepted} rejected_events=0")
    print("fixed_signature_table=true honest_singleton_deliveries=4850 complete_horizon=true")
    print("m2_completion=default_reject_committee_confined_signature_sound_total_slots_clamped_pjf")
    print("payload_relay=anchor_source_13_target_23_child_both_85 all_index1_accepted=true")
    for item in observations:
        if item["slot"] in (10, 11, 12):
            print("STATE " + " ".join(f"{key}={value // UNIT if key in ('support', 'threshold', 'discount', 'full', 'empty') else value}"
                                      for key, value in item.items()) + " weight_unit=1000000000_Gwei")
    assert ledger_observation is not None
    print("LEDGER slot=12 lo=1 sigma=11 " + " ".join(f"{key}={value // UNIT}U"
        for key, value in ledger_observation.items()) + " inequality=true")
    print("RESULT: source confirms child at slot11; honest receiver head excludes child at slot12")
    print("SCOPE: exact-source handler execution with explicit Lean-model external projections")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--consensus-repo", type=Path, required=True)
    args = parser.parse_args()
    check(args.consensus_repo)


if __name__ == "__main__":
    main()
