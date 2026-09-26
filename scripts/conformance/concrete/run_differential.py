#!/usr/bin/env python3
"""Compare pinned Gloas pyspec FFG reads with checked Lean evaluation."""

from __future__ import annotations

import argparse
import json
import linecache
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import traceback


ROOT = Path(__file__).resolve().parents[3]
PIN = "13f391516352f61b3ac5dcaae5be1884d104f86a"


def base(slot: int, count: int = 2, balance: int = 32_000_000_000) -> dict:
    return {
        "slot": slot,
        "header_slot": 0,
        "header_root": 100,
        "validators": [
            {"effective_balance": balance, "slashed": False,
             "activation_epoch": 0, "exit_epoch": 2**64 - 1}
            for _ in range(count)
        ],
        "bits": [False] * 4,
        "previous_justified": [0, 0],
        "current_justified": [0, 0],
        "finalized": [0, 0],
        "previous_participation": [0] * count,
        "current_participation": [0] * count,
        "block_roots": list(range(64)),
        "availability": [False] * 64,
        "latest_block_hash": 0,
        "latest_bid_block_hash": 0,
    }


def cases() -> list[dict]:
    rows = []

    def add(name: str, slot: int, action: str = "pjf", **changes: object) -> None:
        state = base(slot)
        state.update({k: v for k, v in changes.items() if k != "query_slot"})
        row = {"name": name, "action": action, "state": state}
        if "query_slot" in changes:
            row["query_slot"] = changes["query_slot"]
        rows.append(row)

    add("epoch0_start_stub", 0)
    add("epoch0_end_stub", 7, previous_participation=[2, 2])
    add("epoch1_start_stub", 8, current_participation=[2, 2])
    add("epoch1_end_stub", 15, previous_participation=[2, 2])
    add("slot16_previous_support", 16, previous_participation=[2, 2])
    add("slot16_current_empty", 16, current_participation=[0, 0])
    add("epoch_start_fabricated_current_rejected", 16,
        current_participation=[2, 2])
    add("current_support", 23, current_participation=[2, 2])
    add("previous_and_current", 23, previous_participation=[2, 2],
        current_participation=[2, 2])
    add("one_boundary_without_support", 23)
    add("two_boundaries_without_support", 31)
    add("many_boundaries_without_support", 55)
    add("finalize_rule_1", 39, previous_participation=[2, 2],
        bits=[False, True, True, False], previous_justified=[1, 9])
    add("finalize_rule_2", 39, previous_participation=[2, 2],
        bits=[True, True, False, False], previous_justified=[2, 17])
    add("finalize_rule_3", 39, previous_participation=[2, 2],
        current_participation=[2, 2], bits=[False, True, False, False],
        current_justified=[2, 17])
    add("finalize_rule_4", 39, previous_participation=[2, 2],
        current_participation=[2, 2], current_justified=[3, 25])
    add("finalize_order", 39, previous_participation=[2, 2],
        current_participation=[2, 2], bits=[True, True, True, False],
        previous_justified=[1, 9], current_justified=[3, 25])
    floor = base(23, 2, 1_000_000_000)
    rows.append({"name": "balance_floor_below_quorum", "action": "pjf", "state": floor})
    floor = base(23, 1, 1_000_000_000)
    rows.append({"name": "balance_floor_at_increment", "action": "pjf", "state": floor})
    add("root_wrap_valid", 65, "root", query_slot=1)
    add("root_wrap_expired", 65, "root", query_slot=0)
    add("root_current_slot_invalid", 65, "root", query_slot=65)

    for name, start, target in [
        ("one_skipped_boundary", 0, 8),
        ("two_skipped_boundaries", 0, 16),
        ("many_skipped_boundaries", 0, 40),
        ("slot16_gap_from_previous", 14, 17),
        ("root_ring_wraparound", 63, 66),
        ("slots_strict_target", 16, 16),
    ]:
        rows.append({"name": name, "action": "slots", "state": base(start),
                     "target_slot": target})

    def attestation(name: str, state_slot: int, *, data_slot: int = 16,
                    target: list[int] | None = None, source: list[int] | None = None,
                    head: int = 16, index: int = 0,
                    committee_bits: list[bool] | None = None,
                    aggregation_bits: list[bool] | None = None,
                    parent_slot: int = 16, **state_changes: object) -> None:
        state = base(state_slot, 4)
        state.update(state_changes)
        rows.append({
            "name": name, "action": "attestation", "state": state,
            "parent_slot": parent_slot,
            "vote": {
                "aggregation_bits": aggregation_bits if aggregation_bits is not None
                else [True, True],
                "committee_bits": committee_bits if committee_bits is not None
                else [True, False, False, False],
                "data": {"slot": data_slot, "index": index,
                         "beacon_block_root": head,
                         "source": source if source is not None else [0, 0],
                         "target": target if target is not None else [2, 16]},
            },
        })

    attestation("current_same_slot", 17)
    attestation("current_duplicate", 17, current_participation=[7, 7, 0, 0])
    attestation("overlapping_aggregate", 17, current_participation=[7, 0, 0, 0])
    attestation("previous_target_last_inclusion", 31)
    attestation("previous_target_early", 24)
    attestation("first_expired_inclusion", 32)
    attestation("wrong_target_accepted_source", 17, target=[2, 99])
    attestation("invalid_source", 17, source=[1, 9])
    attestation("wire_index_two", 17, index=2)
    attestation("same_slot_index_one", 17, index=1)
    attestation("committee_out_of_count", 17,
                committee_bits=[False, False, True, False],
                aggregation_bits=[True, True])
    attestation("committee_empty_selection", 17,
                committee_bits=[False] * 4, aggregation_bits=[])
    attestation("committee_empty_attesters", 17,
                aggregation_bits=[False, False])
    attestation("aggregation_short", 17, aggregation_bits=[True])
    attestation("aggregation_long", 17, aggregation_bits=[True, True, False])
    attestation("two_committees", 17,
                committee_bits=[True, True, False, False],
                aggregation_bits=[True, True, True, False])
    skipped_roots = list(range(64))
    skipped_roots[15] = 16
    full = [False] * 64
    full[15] = True
    attestation("skipped_slot_full_payload", 17, index=1, parent_slot=15,
                block_roots=skipped_roots, availability=full)
    attestation("skipped_slot_wrong_payload", 17, index=0, parent_slot=15,
                block_roots=skipped_roots, availability=full)

    def sequence_vote(bits: list[bool]) -> dict:
        return {"aggregation_bits": bits,
                "committee_bits": [True, False, False, False],
                "data": {"slot": 16, "index": 0, "beacon_block_root": 16,
                         "source": [0, 0], "target": [2, 16]}}

    rows.append({"name": "duplicate_aggregates", "action": "attestations",
                 "state": base(17, 4), "parent_slot": 16,
                 "votes": [sequence_vote([True, True]), sequence_vote([True, True])]})
    rows.append({"name": "overlapping_aggregates", "action": "attestations",
                 "state": base(17, 4), "parent_slot": 16,
                 "votes": [sequence_vote([True, False]), sequence_vote([True, True])]})

    def transition(name: str, *, start: int = 16, block_slot: int = 17,
                   parent_root: int = 100, oracle_accept: bool = True,
                   parent_block_hash: int = 1, parent_requests_match: bool = False,
                   deposit_count: int = 0, vote_changes: dict | None = None,
                   state_changes: dict | None = None) -> None:
        state = base(start, 4)
        state.update(state_changes or {})
        data = {"slot": 16, "index": 0, "beacon_block_root": 100,
                "source": [0, 0], "target": [2, 100]}
        if vote_changes:
            data.update(vote_changes)
        vote = {"aggregation_bits": [True, True],
                "committee_bits": [True, False, False, False], "data": data}
        rows.append({
            "name": name, "action": "transition", "state": state,
            "oracle_accept": oracle_accept,
            "block": {"slot": block_slot, "parent_root": parent_root,
                      "proposer_index": 0, "root": (100 + block_slot) % 256,
                      "parent_block_hash": parent_block_hash, "block_hash": 2,
                      "parent_requests_empty": True,
                      "parent_requests_match": parent_requests_match,
                      "deposit_count": deposit_count,
                      "attestations": [vote]},
        })

    transition("transition_accept")
    transition("transition_parent_full", parent_block_hash=0,
               parent_requests_match=True)
    transition("transition_oracle_reject", oracle_accept=False)
    transition("transition_bad_slot", block_slot=16)
    transition("transition_bad_parent", parent_root=99)
    transition("transition_bad_source", vote_changes={"source": [1, 9]})
    transition("transition_bad_index", vote_changes={"index": 2})
    transition("transition_deposits", deposit_count=1)
    slashed = base(16, 4)["validators"]
    slashed[0]["slashed"] = True
    transition("transition_slashed_proposer", state_changes={"validators": slashed})
    transition("transition_skipped_slot", block_slot=18)
    transition("transition_genesis_stub", start=0, block_slot=1,
               vote_changes={"slot": 0, "target": [0, 100]})
    return rows


def repeated_root(spec, value: int):
    return spec.Root(bytes([value]) * 32)


def pyspec_result(spec, row: dict) -> dict:
    source = row["state"]
    state = spec.BeaconState()
    state.slot = spec.Slot(source["slot"])
    state.latest_block_header.slot = spec.Slot(source["header_slot"])
    state.validators = spec.Validators(data=[
        spec.Validator(
            effective_balance=spec.Gwei(v["effective_balance"]),
            slashed=spec.Boolean(v["slashed"]),
            activation_epoch=spec.Epoch(v["activation_epoch"]),
            exit_epoch=spec.Epoch(v["exit_epoch"]),
        ) for v in source["validators"]
    ])
    state.justification_bits = spec.JustificationBits(data=[
        spec.Boolean(b) for b in source["bits"]
    ])
    for key, field in [
        ("previous_justified", "previous_justified_checkpoint"),
        ("current_justified", "current_justified_checkpoint"),
        ("finalized", "finalized_checkpoint"),
    ]:
        epoch, root = source[key]
        setattr(state, field, spec.Checkpoint(
            epoch=spec.Epoch(epoch), root=repeated_root(spec, root)))
    state.previous_epoch_participation = spec.EpochParticipation(data=[
        spec.ParticipationFlags(v) for v in source["previous_participation"]
    ])
    state.current_epoch_participation = spec.EpochParticipation(data=[
        spec.ParticipationFlags(v) for v in source["current_participation"]
    ])
    state.block_roots = spec.BlockRoots(data=[
        repeated_root(spec, v) for v in source["block_roots"]
    ])
    state.execution_payload_availability = spec.ExecutionPayloadAvailability(data=[
        spec.Boolean(v) for v in source["availability"]
    ])
    state.latest_block_hash = spec.Hash32(bytes([source["latest_block_hash"]]) * 32)
    state.latest_execution_payload_bid.block_hash = spec.Hash32(
        bytes([source["latest_bid_block_hash"]]) * 32)
    try:
        if row["action"] == "root":
            root = spec.get_block_root_at_slot(state, spec.Slot(row["query_slot"]))
            return {"ok": True, "value": {"root": root[0]}}
        if row["action"] == "attestation":
            v = row["vote"]
            data = v["data"]
            vote = spec.Attestation(
                aggregation_bits=spec.AggregationBits(data=v["aggregation_bits"]),
                committee_bits=spec.CommitteeBits(data=v["committee_bits"]),
                data=spec.AttestationData(
                    slot=spec.Slot(data["slot"]),
                    index=spec.CommitteeIndex(data["index"]),
                    beacon_block_root=repeated_root(spec, data["beacon_block_root"]),
                    source=spec.Checkpoint(epoch=spec.Epoch(data["source"][0]),
                                           root=repeated_root(spec, data["source"][1])),
                    target=spec.Checkpoint(epoch=spec.Epoch(data["target"][0]),
                                           root=repeated_root(spec, data["target"][1])),
                ),
            )
            spec.process_attestation(state, vote, spec.Slot(row["parent_slot"]))
        elif row["action"] == "attestations":
            for item in row["votes"]:
                data = item["data"]
                vote = spec.Attestation(
                    aggregation_bits=spec.AggregationBits(data=item["aggregation_bits"]),
                    committee_bits=spec.CommitteeBits(data=item["committee_bits"]),
                    data=spec.AttestationData(
                        slot=spec.Slot(data["slot"]),
                        index=spec.CommitteeIndex(data["index"]),
                        beacon_block_root=repeated_root(spec, data["beacon_block_root"]),
                        source=spec.Checkpoint(epoch=spec.Epoch(data["source"][0]),
                                               root=repeated_root(spec, data["source"][1])),
                        target=spec.Checkpoint(epoch=spec.Epoch(data["target"][0]),
                                               root=repeated_root(spec, data["target"][1])),
                    ),
                )
                spec.process_attestation(state, vote, spec.Slot(row["parent_slot"]))
        elif row["action"] == "transition":
            block_input = row["block"]
            votes = []
            for item in block_input["attestations"]:
                data = item["data"]
                votes.append(spec.Attestation(
                    aggregation_bits=spec.AggregationBits(data=item["aggregation_bits"]),
                    committee_bits=spec.CommitteeBits(data=item["committee_bits"]),
                    data=spec.AttestationData(
                        slot=spec.Slot(data["slot"]),
                        index=spec.CommitteeIndex(data["index"]),
                        beacon_block_root=repeated_root(spec, data["beacon_block_root"]),
                        source=spec.Checkpoint(epoch=spec.Epoch(data["source"][0]),
                                               root=repeated_root(spec, data["source"][1])),
                        target=spec.Checkpoint(epoch=spec.Epoch(data["target"][0]),
                                               root=repeated_root(spec, data["target"][1])),
                    ),
                ))
            block = spec.BeaconBlock(
                slot=spec.Slot(block_input["slot"]),
                proposer_index=spec.ValidatorIndex(block_input["proposer_index"]),
                parent_root=repeated_root(spec, block_input["parent_root"]),
                state_root=repeated_root(spec, (200 + block_input["slot"]) % 256),
            )
            block.body.attestations = spec.Attestations(data=votes)
            block.body.deposits = spec.Deposits(data=[spec.Deposit()]
                                               * block_input["deposit_count"])
            block.body.signed_execution_payload_bid.message.parent_block_hash = (
                spec.Hash32(bytes([block_input["parent_block_hash"]]) * 32))
            block.body.signed_execution_payload_bid.message.block_hash = (
                spec.Hash32(bytes([block_input["block_hash"]]) * 32))
            spec.verify_block_signature = lambda _state, _block: row["oracle_accept"]
            spec.state_transition(state, spec.SignedBeaconBlock(message=block))
        elif row["action"] == "slots":
            spec.process_slots(state, spec.Slot(row["target_slot"]))
        else:
            spec.process_justification_and_finalization(state)
    except (AssertionError, IndexError) as exc:
        if row["action"] == "transition":
            failure = transition_error_class(exc)
        elif row["action"] == "slots":
            failure = "slot"
        elif row["action"] == "root" or row["action"] == "pjf":
            failure = "root"
        else:
            failure = attestation_error_class(exc)
        return {"ok": False, "error": failure}

    def cp(value):
        return [int(value.epoch), value.root[0]]

    return {"ok": True, "value": {
        "slot": int(state.slot),
        "header_slot": int(state.latest_block_header.slot),
        "header_root": spec.hash_tree_root(state.latest_block_header)[0],
        "bits": [bool(x) for x in state.justification_bits],
        "previous_justified": cp(state.previous_justified_checkpoint),
        "current_justified": cp(state.current_justified_checkpoint),
        "finalized": cp(state.finalized_checkpoint),
        "previous_participation": [int(x) for x in state.previous_epoch_participation],
        "current_participation": [int(x) for x in state.current_epoch_participation],
        "block_roots": [x[0] for x in state.block_roots],
        "availability": [bool(x) for x in state.execution_payload_availability],
        "latest_block_hash": state.latest_block_hash[0],
        "latest_bid_block_hash": state.latest_execution_payload_bid.block_hash[0],
    }}


def transition_error_class(exc: BaseException) -> str:
    frames = traceback.extract_tb(exc.__traceback__)
    for frame in reversed(frames):
        if frame.name in {"process_attestation",
                          "get_attestation_participation_flag_indices",
                          "get_block_root_at_slot", "is_attestation_same_slot"}:
            return attestation_error_class(exc)
        if frame.name == "process_block_header":
            return "header"
        if frame.name == "process_operations":
            return "operations"
        if frame.name == "process_parent_execution_payload":
            return "parentPayload"
        if frame.name == "process_slots":
            return "slot"
        if frame.name == "state_transition":
            return "oracle"
    raise RuntimeError(f"unclassified pyspec transition error: {frames[-1]}")


def attestation_error_class(exc: BaseException) -> str:
    frames = traceback.extract_tb(exc.__traceback__)
    for frame in reversed(frames):
        if frame.name not in {
            "process_attestation", "get_attestation_participation_flag_indices",
            "get_block_root_at_slot", "is_attestation_same_slot",
        }:
            continue
        line = linecache.getline(frame.filename, frame.lineno).strip()
        if frame.name == "get_block_root_at_slot":
            return "root"
        if frame.name == "get_attestation_participation_flag_indices":
            return "payloadIndex" if "data.index" in line else "source"
        if frame.name == "process_attestation":
            if "committee_index <" in line:
                return "committee"
            if "data.target.epoch" in line:
                return "target"
            if "MIN_ATTESTATION_INCLUSION_DELAY" in line:
                return "inclusion"
            if "data.index < 2" in line:
                return "payloadIndex"
            if "aggregation_bits" in line or "committee_attesters" in line:
                return "bitfield"
            if "is_valid_indexed_attestation" in line:
                return "indexed"
    raise RuntimeError(f"unclassified pyspec attestation error: {frames[-1]}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--consensus-repo", required=True, type=Path)
    args = parser.parse_args()
    revision = subprocess.check_output(
        ["git", "-C", str(args.consensus_repo), "rev-parse", "HEAD"], text=True
    ).strip()
    if revision != PIN:
        print(f"pyspec revision differs: {revision}", file=sys.stderr)
        return 2
    sys.path.insert(0, str(args.consensus_repo / "tests/core/pyspec"))
    from eth_consensus_specs.gloas import minimal as spec

    # Fixed schedule and BLS-disabled oracle mode. These replace only source
    # committee reads and opaque checks; FFG guards and writes run in pyspec.
    spec.get_committee_count_per_slot = lambda state, epoch: 2
    spec.get_beacon_committee = lambda state, slot, index: (
        [spec.ValidatorIndex(0), spec.ValidatorIndex(1)] if index == 0 else
        [spec.ValidatorIndex(2), spec.ValidatorIndex(3)] if index == 1 else []
    )
    spec.is_valid_indexed_attestation = lambda state, vote: (
        0 < len(vote.attesting_indices) <=
        spec.MAX_VALIDATORS_PER_COMMITTEE * spec.MAX_COMMITTEES_PER_SLOT
        and list(vote.attesting_indices) == sorted(set(vote.attesting_indices))
        and all(i < len(state.validators) for i in vote.attesting_indices)
    )
    spec.get_base_reward = lambda state, index: 0
    spec.get_beacon_proposer_index = lambda state: spec.ValidatorIndex(0)
    spec.increase_balance = lambda state, index, amount: None
    spec.process_withdrawals = lambda state: None
    spec.process_randao = lambda state, body: None
    spec.process_eth1_data = lambda state, body: None
    spec.process_sync_aggregate = lambda state, aggregate: None
    spec.process_execution_payload_bid = lambda state, signed_bid: setattr(
        state, "latest_execution_payload_bid", signed_bid.message)
    spec.hash_tree_root = lambda value: repeated_root(spec, (
        100 + int(value.slot) if isinstance(value, spec.BeaconBlockHeader)
        else 200 + int(value.slot) if isinstance(value, spec.BeaconState) else 0
    ) % 256)
    for name in (
        "process_inactivity_updates", "process_rewards_and_penalties",
        "process_registry_updates", "process_slashings", "process_eth1_data_reset",
        "process_pending_deposits", "process_pending_consolidations",
        "process_builder_pending_payments", "process_effective_balance_updates",
        "process_slashings_reset", "process_randao_mixes_reset",
        "process_historical_summaries_update", "process_sync_committee_updates",
        "process_proposer_lookahead", "process_ptc_window",
    ):
        setattr(spec, name, lambda state: None)

    rows = cases()
    expected = [pyspec_result(spec, row) for row in rows]
    bad_initial = json.loads(json.dumps(next(
        row for row in rows if row["name"] == "transition_accept")))
    bad_initial["name"] = "bad_initial_state"
    bad_initial["state"]["current_participation"].pop()
    lean_rows = [*rows, bad_initial]
    with tempfile.TemporaryDirectory(prefix="ffg-diff-") as temp:
        input_path = Path(temp) / "cases.json"
        input_path.write_text(json.dumps(lean_rows), encoding="utf-8")
        result = subprocess.run(
            ["lake", "env", "lean", "--run",
             "scripts/conformance/concrete/FFGDifferential.lean", str(input_path)],
            cwd=ROOT, text=True, capture_output=True,
            env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}, timeout=600,
        )
    if result.returncode:
        print(result.stderr or result.stdout, file=sys.stderr)
        return result.returncode
    actual = [json.loads(line) for line in result.stdout.splitlines() if line.strip()]
    if len(actual) != len(lean_rows):
        print(f"Lean evaluation count differs: {len(actual)} != {len(lean_rows)}", file=sys.stderr)
        return 1
    differences = 0
    for row, want, got in zip(rows, expected, actual[:-1], strict=True):
        if want != got:
            differences += 1
            print(f"MISMATCH {row['name']}: pyspec={want} lean={got}", file=sys.stderr)
    if actual[-1] != {"ok": False, "error": "state"}:
        differences += 1
        print(f"MISMATCH bad_initial_state: lean={actual[-1]}", file=sys.stderr)
    print(f"concrete differential: cases={len(rows)} agree={len(rows)-differences} "
          f"differences={differences}; structural_bad_state=1")
    return 1 if differences else 0


if __name__ == "__main__":
    raise SystemExit(main())
