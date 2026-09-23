"""Execute pinned Gloas source to show the payload-delivery proof obstacle.

This is a source-function projection fixture, not a generated pyspec trace or
an accepted Lean execution. Fork choice, attestation validation/application,
block/envelope application, and the complete FCR handler use unchanged source bodies.
The fixture supplies projected state transitions, committee lists, root
identities, and successful signature checks. Envelope data and execution
verification use the model's external projection boundary. Only the sender
receives that valid envelope event. The new payload_envelope_relay synchrony
field excludes this missing-envelope pattern within its delivery horizon.
No source file is changed.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace

from gloas_full_instance_obstacle import (
    Checkpoint,
    GloasNode,
    PIN,
    source_functions,
)


UNIT = 1_000_000_000
ANCHOR, BLOCK, SIBLING = 1, 2, 3


class Record(SimpleNamespace):
    def copy(self):
        return deepcopy(self)


@dataclass(frozen=True)
class Message:
    slot: int
    root: int
    payload_present: bool


def load_source(repo: Path) -> dict:
    env = {
        "Root": int,
        "UINT64_MAX": 2**64 - 1,
        "BASIS_POINTS": 10000,
        "Slot": int,
        "Epoch": int,
        "Gwei": int,
        "Uint64": int,
        "Uint8": int,
        "ValidatorIndex": int,
        "CommitteeIndex": int,
        "ForkChoiceNode": GloasNode,
        "LatestMessage": Message,
        "Checkpoint": Checkpoint,
        "FastConfirmationStore": Record,
        "Store": Record,
        "EXECUTION_ENGINE": Record(),
        "SLOTS_PER_EPOCH": 32,
        "SLOT_DURATION_MS": 12000,
        "GENESIS_SLOT": 0,
        "GENESIS_EPOCH": 0,
        "EFFECTIVE_BALANCE_INCREMENT": UNIT,
        "PROPOSER_SCORE_BOOST": 40,
        "CONFIRMATION_BYZANTINE_THRESHOLD": 25,
        "COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR": 5,
        "MIN_SEED_LOOKAHEAD": 1,
        "REORG_HEAD_WEIGHT_THRESHOLD": 20,
        "PAYLOAD_STATUS_EMPTY": 0,
        "PAYLOAD_STATUS_FULL": 1,
        "PAYLOAD_STATUS_PENDING": 2,
        "PTC_SIZE": 512,
        "PAYLOAD_TIMELY_THRESHOLD": 256,
        "DATA_AVAILABILITY_TIMELY_THRESHOLD": 256,
        "ATTESTATION_TIMELINESS_INDEX": 0,
        "PTC_TIMELINESS_INDEX": 1,
        "ATTESTATION_DUE_BPS_GLOAS": 2500,
        "PAYLOAD_ATTESTATION_DUE_BPS": 7500,
        "INTERVALS_PER_SLOT": 3,
    }
    for path in (
        "specs/phase0/beacon-chain.md",
        "specs/phase0/fork-choice.md",
        "specs/phase0/fast-confirmation.md",
        "specs/gloas/fork-choice.md",
        "specs/gloas/fast-confirmation.md",
    ):
        for body in source_functions(repo, path,
                local_override=path == "specs/gloas/fast-confirmation.md").values():
            exec("from __future__ import annotations\n" + body, env)

    def transition(state, signed_block, validate_result=True):
        assert validate_result
        state.slot = signed_block.message.slot
        state.identity = 100 + signed_block.message.root

    def verify_envelope(state, signed_envelope, execution_engine):
        assert state.slot == 1
        assert signed_envelope.message.beacon_block_root == BLOCK
        assert signed_envelope.message.parent_beacon_block_root == ANCHOR
        assert signed_envelope.message.identity == 10000 + BLOCK

    # The same projection boundaries used by the Lean model. These do not
    # alter any selected fork-choice or FCR function body.
    env.update(
        hash_tree_root=lambda value: value.root if hasattr(value, "root") else value.identity,
        get_beacon_committee=lambda state, slot, index: list(range(slot * 100, (slot + 1) * 100)),
        get_committee_count_per_slot=lambda state, epoch: 1,
        get_indexed_attestation=lambda state, attestation: attestation,
        is_valid_indexed_attestation=lambda state, attestation: True,
        state_transition=transition,
        process_justification_and_finalization=lambda state: None,
        is_data_available=lambda root: root == BLOCK,
        verify_execution_payload_envelope=verify_envelope,
    )
    return env


def block(root: int, slot: int) -> Record:
    return Record(
        root=root,
        slot=slot,
        parent_root=ANCHOR if root != ANCHOR else 0,
        proposer_index=slot * 100,
        body=Record(
            signed_execution_payload_bid=Record(
                message=Record(block_hash=1000 + root, parent_block_hash=0)
            ),
            payload_attestations=[],
        ),
    )


def initial_store(spec: dict) -> Record:
    checkpoint = Checkpoint(0, ANCHOR)
    validators = [
        Record(effective_balance=UNIT, slashed=False, activation_epoch=0, exit_epoch=2**64 - 1)
        for _ in range(3200)
    ]
    state = Record(
        identity=100 + ANCHOR,
        genesis_time=0,
        slot=0,
        validators=validators,
        current_justified_checkpoint=checkpoint,
        finalized_checkpoint=checkpoint,
    )
    anchor = block(ANCHOR, 0)
    anchor.state_root = spec["hash_tree_root"](state)
    return spec["get_forkchoice_store"](state, anchor)


def attestation(slot: int, root: int, index: int) -> Record:
    return Record(
        attesting_indices=list(range(slot * 100, (slot + 1) * 100)),
        data=Record(
            slot=slot,
            index=index,
            beacon_block_root=root,
            source=Checkpoint(0, ANCHOR),
            target=Checkpoint(0, ANCHOR),
        ),
    )


def check(repo: Path) -> None:
    spec = load_source(repo)
    sender = initial_store(spec)
    receiver = deepcopy(sender)
    fcr = spec["get_fast_confirmation_store"](sender)

    # Slot-1 voters vote the anchor before B arrives. All these votes are
    # delivered at the start of slot 2. No missing pre-synchrony votes are used.
    for store in (sender, receiver):
        spec["on_tick"](store, 12)
        spec["on_attestation"](store, attestation(0, ANCHOR, 0))
    spec["on_fast_confirmation"](fcr)
    assert spec["get_head"](sender).root == ANCHOR
    first_vote = attestation(1, ANCHOR, 0)
    for store in (sender, receiver):
        spec["on_tick"](store, 23)
        spec["on_block"](store, Record(message=block(BLOCK, 1)))
    envelope = Record(message=Record(
        beacon_block_root=BLOCK,
        parent_beacon_block_root=ANCHOR,
        identity=10000 + BLOCK,
    ))
    spec["on_execution_payload_envelope"](sender, envelope)

    # Validators 100*s .. 100*s+99 vote at slot s. The receiver can be
    # validator 0: it votes the anchor at slot 0 and has no assignment in
    # slots 1..7. All slot-2..6 voters have the sender's payload-holding view.
    # Aggregates below represent their equal-data singleton honest votes.
    rejected = 0
    for current_slot in range(2, 7):
        for store in (sender, receiver):
            spec["on_tick"](store, current_slot * 12)
        vote = first_vote if current_slot == 2 else attestation(current_slot - 1, BLOCK, 1)
        spec["on_attestation"](sender, vote)
        try:
            spec["on_attestation"](receiver, vote)
        except AssertionError as error:
            assert current_slot > 2
            assert not spec["is_payload_verified"](receiver, BLOCK)
            # The failed source assertion is the index-1 payload gate.
            frame = error.__traceback__
            while frame.tb_next is not None:
                frame = frame.tb_next
            assert frame.tb_frame.f_code.co_name == "validate_on_attestation"
            rejected += len(vote.attesting_indices)
        assert spec["get_head"](sender) == GloasNode(BLOCK, 1)
        assert spec["get_head"](receiver) == GloasNode(BLOCK, 0)
        spec["on_fast_confirmation"](fcr)

    balance = sender.checkpoint_states[sender.justified_checkpoint]
    support = spec["get_attestation_score"](sender, spec["get_node_for_root"](BLOCK), balance)
    threshold = spec["compute_safety_threshold"](sender, BLOCK, balance)
    assert (support, threshold) == (400 * UNIT, 395 * UNIT)
    assert spec["is_one_confirmed"](sender, balance, BLOCK)
    assert fcr.confirmed_root == BLOCK
    assert rejected == 400
    assert spec["get_attestation_score"](receiver, spec["get_node_for_root"](BLOCK), balance) == 0
    print(f"slot=6 sender_support={support} threshold={threshold} confirmed_root={fcr.confirmed_root}")
    print(f"delivered_index1_votes=400 receiver_rejected={rejected} receiver_B_support=0")

    # B remains the source head throughout slot 6, so the next committee's
    # honest index-1 votes are again votes for its own head.
    for store in (sender, receiver):
        spec["on_tick"](store, 84)
    last_vote = attestation(6, BLOCK, 1)
    spec["on_attestation"](sender, last_vote)
    try:
        spec["on_attestation"](receiver, last_vote)
    except AssertionError:
        pass
    else:
        raise AssertionError("receiver unexpectedly accepted a full-payload vote")
    for store in (sender, receiver):
        spec["on_block"](store, Record(message=block(SIBLING, 7)))
    sender_head = spec["get_head"](sender)
    receiver_head = spec["get_head"](receiver)
    assert sender_head.root == BLOCK
    assert receiver_head.root == SIBLING
    assert not spec["is_ancestor"](receiver, receiver_head, spec["get_node_for_root"](BLOCK))
    print(f"slot=7 sender_head={sender_head} receiver_head={receiver_head}")
    print(f"receiver_proposer_boost={spec['get_proposer_score'](receiver)}")
    print(f"pin={PIN}")
    print("OBSTACLE: delivered honest index-1 votes can be rejected without payload relay")
    print("SCOPE: exact source function projection; no full pyspec or Lean accepted-execution witness")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--consensus-repo", type=Path, required=True)
    check(parser.parse_args().consensus_repo)


if __name__ == "__main__":
    main()
