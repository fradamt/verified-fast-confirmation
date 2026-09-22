"""Export Python fast-confirmation calls as schema-versioned JSON Lines."""

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
            }
            for root, block in store.blocks.items()
        ],
        "block_states": [
            {"root": _root(root), "state": _state(spec, state)}
            for root, state in store.block_states.items()
        ],
        "block_timeliness": [
            {"root": _root(root), "timely": bool(timely)}
            for root, timely in store.block_timeliness.items()
        ],
        "checkpoint_states": [
            {"checkpoint": _checkpoint(checkpoint), "state": _state(spec, state)}
            for checkpoint, state in store.checkpoint_states.items()
        ],
        "latest_messages": [
            {
                "index": _int(index),
                "epoch": _int(message.epoch),
                "root": _root(message.root),
            }
            for index, message in sorted(store.latest_messages.items(), key=lambda item: _int(item[0]))
        ],
        "unrealized_justifications": [
            {"root": _root(root), "checkpoint": _checkpoint(checkpoint)}
            for root, checkpoint in store.unrealized_justifications.items()
        ],
    }


def _fcr_store(fcr_store: Any) -> dict[str, Any]:
    fields = {
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
    if hasattr(fcr_store, "current_epoch_greatest_unrealized_checkpoint"):
        fields["current_epoch_greatest_unrealized_checkpoint"] = _checkpoint(
            fcr_store.current_epoch_greatest_unrealized_checkpoint
        )
    return fields


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
        "attestation_due_bps": _int(spec.config.ATTESTATION_DUE_BPS),
        "min_seed_lookahead": _int(spec.MIN_SEED_LOOKAHEAD),
    }


def _ambiguity_guard(
    seen: dict[str, dict[str, Any]],
    function: str,
    key_data: tuple[Any, ...],
    answer: Any,
    test_id: str,
) -> None:
    key = json.dumps(_without_state_ids(key_data), separators=(",", ":"), sort_keys=True)
    previous = seen.setdefault(function, {})
    answer_key = json.dumps(answer, separators=(",", ":"), sort_keys=True)
    if key in previous and previous[key] != answer_key:
        raise RuntimeError(f"projection ambiguity {function} test_id={test_id}")
    previous[key] = answer_key


def _without_state_ids(value: Any) -> Any:
    """Remove informational state roots from projection keys."""
    if isinstance(value, dict):
        return {
            key: _without_state_ids(item)
            for key, item in value.items()
            if key != "id"
        }
    if isinstance(value, tuple):
        return tuple(_without_state_ids(item) for item in value)
    if isinstance(value, list):
        return [_without_state_ids(item) for item in value]
    return value


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
    seen: dict[str, dict[str, str]] = {}

    def get_beacon_committee(state: Any, slot: Any, index: Any) -> Any:
        before = _state(spec, state)
        result = originals["get_beacon_committee"](state, slot, index)
        answer = {"state": before, "slot": _int(slot), "index": _int(index), "result": [_int(i) for i in result]}
        _ambiguity_guard(
            seen,
            "get_beacon_committee",
            (before, _int(slot), _int(index)),
            answer["result"],
            test_id,
        )
        externals["get_beacon_committee"].append(answer)
        return result

    def get_committee_count_per_slot(state: Any, epoch: Any) -> Any:
        before = _state(spec, state)
        result = originals["get_committee_count_per_slot"](state, epoch)
        answer = {"state": before, "epoch": _int(epoch), "result": _int(result)}
        _ambiguity_guard(
            seen,
            "get_committee_count_per_slot",
            (before, _int(epoch)),
            answer["result"],
            test_id,
        )
        externals["get_committee_count_per_slot"].append(answer)
        return result

    def process_slots(state: Any, slot: Any) -> Any:
        before = _state(spec, state)
        result = originals["process_slots"](state, slot)
        answer = {"state": before, "slot": _int(slot), "result": _state(spec, state)}
        _ambiguity_guard(
            seen,
            "process_slots",
            (before, _int(slot)),
            answer["result"],
            test_id,
        )
        externals["process_slots"].append(answer)
        return result

    def process_justification_and_finalization(state: Any) -> Any:
        before = _state(spec, state)
        result = originals["process_justification_and_finalization"](state)
        answer = {"state": before, "result": _state(spec, state)}
        _ambiguity_guard(
            seen,
            "process_justification_and_finalization",
            (before,),
            answer["result"],
            test_id,
        )
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
        "schema": 2 if "current_epoch_greatest_unrealized_checkpoint" in fcr_before else 1,
        "test_id": test_id,
        "fork": str(spec.fork),
        "preset": str(spec.config.PRESET_BASE),
        "call_index": call_index,
        "config": _config(spec),
        "store": store_before,
        "fcr_before": fcr_before,
        "fcr_after": _fcr_store(fcr_store),
        "externals": externals,
    }
    _writer.write(json.dumps(record, separators=(",", ":")) + "\n")
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
