"""Export Gloas fast-confirmation calls as schema v2 JSON Lines."""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any, Callable

import pytest


_current_item: pytest.Item | None = None
_original_run_fast_confirmation: Callable[..., Any] | None = None
_writer: Any = None
_call_indices: dict[str, int] = {}


def _int(value: Any) -> int:
    return int(value)


def _root(value: Any) -> str:
    encoded = bytes(value).hex()
    if len(encoded) != 64:
        raise ValueError(f"expected a 32-byte root, got {len(encoded) // 2} bytes")
    return f"0x{encoded}"


def _checkpoint(checkpoint: Any) -> dict[str, Any]:
    return {"epoch": _int(checkpoint.epoch), "root": _root(checkpoint.root)}


def _state(spec: Any, state: Any) -> dict[str, Any]:
    return {
        "id": _root(spec.hash_tree_root(state)),
        "genesis_time": _int(state.genesis_time),
        "slot": _int(state.slot),
        "validators": [
            {
                "effective_balance": _int(validator.effective_balance),
                "slashed": bool(validator.slashed),
                "activation_epoch": _int(validator.activation_epoch),
                "exit_epoch": _int(validator.exit_epoch),
            }
            for validator in state.validators
        ],
        "current_justified_checkpoint": _checkpoint(state.current_justified_checkpoint),
        "finalized_checkpoint": _checkpoint(state.finalized_checkpoint),
    }


def _node(node: Any) -> dict[str, Any]:
    return {"root": _root(node.root), "payload_status": _int(node.payload_status)}


def _payload_attestation_data(data: Any) -> dict[str, Any]:
    return {
        "beacon_block_root": _root(data.beacon_block_root),
        "slot": _int(data.slot),
        "payload_present": bool(data.payload_present),
        "blob_data_available": bool(data.blob_data_available),
    }


def _store(spec: Any, store: Any) -> dict[str, Any]:
    return {
        "time": _int(store.time),
        "genesis_time": _int(store.genesis_time),
        "justified_checkpoint": _checkpoint(store.justified_checkpoint),
        "finalized_checkpoint": _checkpoint(store.finalized_checkpoint),
        "unrealized_justified_checkpoint": _checkpoint(store.unrealized_justified_checkpoint),
        "unrealized_finalized_checkpoint": _checkpoint(store.unrealized_finalized_checkpoint),
        "proposer_boost_root": _root(store.proposer_boost_root),
        "equivocating_indices": sorted(_int(index) for index in store.equivocating_indices),
        "blocks": [
            {
                "root": _root(root),
                "slot": _int(block.slot),
                "parent_root": _root(block.parent_root),
                "proposer_index": _int(block.proposer_index),
                "parent_block_hash": _root(block.body.signed_execution_payload_bid.message.parent_block_hash),
                "block_hash": _root(block.body.signed_execution_payload_bid.message.block_hash),
                "payload_attestations": [
                    {
                        "attesting_indices": [_int(i) for i in spec.get_indexed_payload_attestation(
                            store.block_states[root], attestation
                        ).attesting_indices],
                        "data": _payload_attestation_data(attestation.data),
                        "signature": _root(spec.hash_tree_root(attestation.signature)),
                    }
                    for attestation in block.body.payload_attestations
                ],
            }
            for root, block in store.blocks.items()
        ],
        "block_states": [
            {"root": _root(root), "state": _state(spec, state)}
            for root, state in store.block_states.items()
        ],
        "block_timeliness": [
            {"root": _root(root), "timely": [bool(value) for value in timely]}
            for root, timely in store.block_timeliness.items()
        ],
        "checkpoint_states": [
            {"checkpoint": _checkpoint(checkpoint), "state": _state(spec, state)}
            for checkpoint, state in store.checkpoint_states.items()
        ],
        "latest_messages": [
            {
                "index": _int(index),
                "slot": _int(message.slot),
                "payload_present": bool(message.payload_present),
                "root": _root(message.root),
            }
            for index, message in sorted(store.latest_messages.items(), key=lambda item: _int(item[0]))
        ],
        "payloads": [
            {
                "root": _root(root),
                "beacon_block_root": _root(envelope.beacon_block_root),
                "parent_beacon_block_root": _root(envelope.parent_beacon_block_root),
                "identity": _root(spec.hash_tree_root(envelope)),
            }
            for root, envelope in store.payloads.items()
        ],
        "payload_timeliness_vote": [
            {"root": _root(root), "votes": [None if vote is None else bool(vote) for vote in votes]}
            for root, votes in store.payload_timeliness_vote.items()
        ],
        "payload_data_availability_vote": [
            {"root": _root(root), "votes": [None if vote is None else bool(vote) for vote in votes]}
            for root, votes in store.payload_data_availability_vote.items()
        ],
        "unrealized_justifications": [
            {"root": _root(root), "checkpoint": _checkpoint(checkpoint)}
            for root, checkpoint in store.unrealized_justifications.items()
        ],
    }


def _fcr_store(fcr_store: Any) -> dict[str, Any]:
    return {
        "confirmed_root": _root(fcr_store.confirmed_root),
        "previous_epoch_observed_justified_checkpoint": _checkpoint(
            fcr_store.previous_epoch_observed_justified_checkpoint
        ),
        "current_epoch_observed_justified_checkpoint": _checkpoint(
            fcr_store.current_epoch_observed_justified_checkpoint
        ),
        "previous_epoch_greatest_unrealized_checkpoint": _checkpoint(
            fcr_store.previous_epoch_greatest_unrealized_checkpoint
        ),
        "previous_slot_head": _root(fcr_store.previous_slot_head),
        "current_slot_head": _root(fcr_store.current_slot_head),
    }


def _config(spec: Any) -> dict[str, Any]:
    return {
        "slots_per_epoch": _int(spec.SLOTS_PER_EPOCH),
        "slot_duration_ms": _int(spec.config.SLOT_DURATION_MS),
        "proposer_score_boost": _int(spec.config.PROPOSER_SCORE_BOOST),
        "confirmation_byzantine_threshold": _int(
            spec.config.CONFIRMATION_BYZANTINE_THRESHOLD
        ),
        "committee_weight_estimation_adjustment_factor": _int(
            spec.COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR
        ),
        "effective_balance_increment": _int(spec.EFFECTIVE_BALANCE_INCREMENT),
        "attestation_due_bps": _int(spec.config.ATTESTATION_DUE_BPS_GLOAS),
        "ptc_size": _int(spec.PTC_SIZE),
        "payload_due_bps": _int(spec.config.PAYLOAD_DUE_BPS),
        "payload_attestation_due_bps": _int(spec.config.PAYLOAD_ATTESTATION_DUE_BPS),
        "reorg_head_weight_threshold": _int(spec.config.REORG_HEAD_WEIGHT_THRESHOLD),
        "min_seed_lookahead": _int(spec.MIN_SEED_LOOKAHEAD),
    }


def _ambiguity_guard(
    seen: dict[str, dict[str, Any]],
    function: str,
    key_data: tuple[Any, ...],
    answer: Any,
    test_id: str,
) -> None:
    key = json.dumps(key_data, separators=(",", ":"), sort_keys=True)
    previous = seen.setdefault(function, {})
    answer_key = json.dumps(answer, separators=(",", ":"), sort_keys=True)
    if key in previous and previous[key] != answer_key:
        raise RuntimeError(f"projection ambiguity {function} test_id={test_id}")
    previous[key] = answer_key


def _encode_large_integers(value: Any) -> Any:
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return str(value) if value > 2**53 else value
    if isinstance(value, dict):
        return {key: _encode_large_integers(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_encode_large_integers(item) for item in value]
    return value


def _attach_read_views(record: dict[str, Any]) -> None:
    """Build finite source read views from all calls reached in this record."""
    committees: dict[str, dict[tuple[int, int], list[int]]] = {}
    counts: dict[str, dict[int, int]] = {}
    for answer in record["externals"]["get_beacon_committee"]:
        key = (answer["slot"], answer["index"])
        values = committees.setdefault(answer["state"]["id"], {})
        if key in values and values[key] != answer["result"]:
            raise RuntimeError(f"inconsistent committee read test_id={record['test_id']}")
        values[key] = answer["result"]
    for answer in record["externals"]["get_committee_count_per_slot"]:
        values = counts.setdefault(answer["state"]["id"], {})
        if answer["epoch"] in values and values[answer["epoch"]] != answer["result"]:
            raise RuntimeError(f"inconsistent committee count test_id={record['test_id']}")
        values[answer["epoch"]] = answer["result"]

    def visit(value: Any) -> None:
        if isinstance(value, dict):
            if "id" in value and "validators" in value:
                identity = value["id"]
                value["beacon_committee_reads"] = [
                    {"slot": slot, "index": index, "result": result}
                    for (slot, index), result in sorted(committees.get(identity, {}).items())
                ]
                value["committee_count_reads"] = [
                    {"epoch": epoch, "result": result}
                    for epoch, result in sorted(counts.get(identity, {}).items())
                ]
            for item in value.values():
                visit(item)
        elif isinstance(value, list):
            for item in value:
                visit(item)

    visit(record)


def _check_projection_answers(record: dict[str, Any]) -> None:
    seen: dict[str, dict[str, Any]] = {}
    for function, answers in record["externals"].items():
        for answer in answers:
            key = tuple((key, value) for key, value in answer.items() if key != "result")
            _ambiguity_guard(seen, function, key, answer["result"], record["test_id"])


def _wrap_externals(spec: Any, test_id: str, externals: dict[str, list[dict[str, Any]]]):
    originals = {
        name: getattr(spec, name)
        for name in (
            "get_beacon_committee",
            "get_committee_count_per_slot",
            "process_slots",
            "process_justification_and_finalization",
        )
    }

    def get_beacon_committee(state: Any, slot: Any, index: Any) -> Any:
        before = _state(spec, state)
        result = originals["get_beacon_committee"](state, slot, index)
        answer = {"state": before, "slot": _int(slot), "index": _int(index), "result": [_int(i) for i in result]}
        externals["get_beacon_committee"].append(answer)
        return result

    def get_committee_count_per_slot(state: Any, epoch: Any) -> Any:
        before = _state(spec, state)
        result = originals["get_committee_count_per_slot"](state, epoch)
        answer = {"state": before, "epoch": _int(epoch), "result": _int(result)}
        externals["get_committee_count_per_slot"].append(answer)
        return result

    def process_slots(state: Any, slot: Any) -> Any:
        before = _state(spec, state)
        result = originals["process_slots"](state, slot)
        answer = {"state": before, "slot": _int(slot), "result": _state(spec, state)}
        externals["process_slots"].append(answer)
        return result

    def process_justification_and_finalization(state: Any) -> Any:
        before = _state(spec, state)
        result = originals["process_justification_and_finalization"](state)
        answer = {"state": before, "result": _state(spec, state)}
        externals["process_justification_and_finalization"].append(answer)
        return result

    wrappers = {
        "get_beacon_committee": get_beacon_committee,
        "get_committee_count_per_slot": get_committee_count_per_slot,
        "process_slots": process_slots,
        "process_justification_and_finalization": process_justification_and_finalization,
    }
    for name, wrapper in wrappers.items():
        setattr(spec, name, wrapper)
    return originals


def _capture(self: Any) -> None:
    if _writer is None:
        raise RuntimeError("FCR_TRACE_OUT is not configured")
    spec = self.spec
    if str(spec.fork) != "gloas":
        raise RuntimeError("schema v2 requires Gloas; pre-Gloas stores are historical")
    fcr_store = self.fcr_store
    test_id = _current_item.nodeid if _current_item is not None else "<unknown>"
    call_index = _call_indices.get(test_id, 0)
    _call_indices[test_id] = call_index + 1

    store_before = _store(spec, fcr_store.store)
    fcr_before = _fcr_store(fcr_store)
    externals: dict[str, list[dict[str, Any]]] = {
        "get_beacon_committee": [],
        "get_committee_count_per_slot": [],
        "process_slots": [],
        "process_justification_and_finalization": [],
    }
    originals = _wrap_externals(spec, test_id, externals)
    try:
        # Fill the only state-read domain used by Gloas head scoring. These
        # queries also cover paths that the extra head call does not take.
        store = fcr_store.store
        if store.proposer_boost_root != spec.Root():
            boost = store.blocks[store.proposer_boost_root]
            parent = store.blocks[boost.parent_root]
            if parent.slot + 1 >= boost.slot:
                state = store.block_states[boost.parent_root]
                epoch = spec.compute_epoch_at_slot(parent.slot)
                count = spec.get_committee_count_per_slot(state, epoch)
                for index in range(count):
                    spec.get_beacon_committee(state, parent.slot, spec.CommitteeIndex(index))
        head_before = _node(spec.get_head(fcr_store.store))
        spec.on_fast_confirmation(fcr_store)
    finally:
        for name, original in originals.items():
            setattr(spec, name, original)

    store_after = _store(spec, fcr_store.store)
    if store_before != store_after:
        for field in store_before:
            if store_before[field] != store_after[field]:
                raise RuntimeError(f"store mutation {field} test_id={test_id}")
        raise RuntimeError(f"store mutation unknown test_id={test_id}")

    record = {
        "schema": 2,
        "head_before": head_before,
        "test_id": test_id,
        "fork": str(spec.fork),
        "preset": str(spec.config.PRESET_BASE),
        "call_index": call_index,
        "config": _config(spec),
        "store": store_before,
        "fcr_before": fcr_before,
        "fcr_after": _fcr_store(fcr_store),
        "safe_execution_block_hash_after": _root(spec.get_safe_execution_block_hash(fcr_store)),
        "externals": externals,
    }
    _attach_read_views(record)
    _check_projection_answers(record)
    _writer.write(json.dumps(_encode_large_integers(record), separators=(",", ":")) + "\n")
    _writer.flush()

    from eth_consensus_specs.test.helpers.fast_confirmation import output_fast_confirmation_checks

    output_fast_confirmation_checks(spec, fcr_store, self.test_steps)


def pytest_configure(config: pytest.Config) -> None:
    global _original_run_fast_confirmation, _writer
    output = os.environ.get("FCR_TRACE_OUT")
    if not output:
        raise RuntimeError("FCR_TRACE_OUT is required by fcr_trace_plugin")
    output_path = Path(output)
    worker_id = getattr(config, "workerinput", {}).get("workerid")
    if worker_id:
        output_path = output_path.with_name(f"{output_path.stem}.{worker_id}{output_path.suffix}")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    _writer = output_path.open("w", encoding="utf-8")

    from eth_consensus_specs.test.helpers.fast_confirmation import FCRTest

    if _original_run_fast_confirmation is None:
        _original_run_fast_confirmation = FCRTest.run_fast_confirmation
        FCRTest.run_fast_confirmation = _capture


def pytest_unconfigure(config: pytest.Config) -> None:
    global _writer
    if _writer is not None:
        _writer.close()
        _writer = None


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_call(item: pytest.Item):
    global _current_item
    _current_item = item
    try:
        yield
    finally:
        _current_item = None
