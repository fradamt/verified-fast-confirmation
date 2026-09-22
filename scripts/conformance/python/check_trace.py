"""Check FCR trace shape and print compact trace counts."""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = re.compile(r"^0x[0-9a-f]{64}$")
CONFIG_KEYS = {
    "slots_per_epoch",
    "slot_duration_ms",
    "proposer_score_boost",
    "confirmation_byzantine_threshold",
    "committee_weight_estimation_adjustment_factor",
    "effective_balance_increment",
    "attestation_due_bps",
    "min_seed_lookahead",
}
STORE_KEYS = {
    "time",
    "genesis_time",
    "justified_checkpoint",
    "finalized_checkpoint",
    "unrealized_justified_checkpoint",
    "unrealized_finalized_checkpoint",
    "proposer_boost_root",
    "equivocating_indices",
    "blocks",
    "block_states",
    "block_timeliness",
    "checkpoint_states",
    "latest_messages",
    "unrealized_justifications",
}
FCR_KEYS = {
    "confirmed_root",
    "previous_epoch_observed_justified_checkpoint",
    "current_epoch_observed_justified_checkpoint",
    "previous_epoch_greatest_unrealized_checkpoint",
    "previous_slot_head",
    "current_slot_head",
}
EXTERNAL_KEYS = {
    "get_beacon_committee",
    "get_committee_count_per_slot",
    "process_slots",
    "process_justification_and_finalization",
}


def fail(message: str) -> None:
    raise ValueError(message)


def integer(value: Any, path: str) -> int:
    if isinstance(value, bool):
        fail(f"{path}: boolean is not an integer")
    if isinstance(value, int):
        return value
    if isinstance(value, str) and value.isdecimal():
        return int(value)
    fail(f"{path}: expected JSON integer or decimal string")


def root(value: Any, path: str) -> None:
    if not isinstance(value, str) or ROOT.fullmatch(value) is None:
        fail(f"{path}: invalid root")


def exact_keys(value: Any, expected: set[str], path: str) -> None:
    if not isinstance(value, dict) or set(value) != expected:
        fail(f"{path}: expected keys {sorted(expected)}")


def checkpoint(value: Any, path: str) -> None:
    exact_keys(value, {"epoch", "root"}, path)
    integer(value["epoch"], f"{path}.epoch")
    root(value["root"], f"{path}.root")


def state(value: Any, path: str) -> None:
    exact_keys(
        value,
        {
            "id",
            "genesis_time",
            "slot",
            "validators",
            "current_justified_checkpoint",
            "finalized_checkpoint",
        },
        path,
    )
    root(value["id"], f"{path}.id")
    integer(value["genesis_time"], f"{path}.genesis_time")
    integer(value["slot"], f"{path}.slot")
    if not isinstance(value["validators"], list):
        fail(f"{path}.validators: expected list")
    for index, validator in enumerate(value["validators"]):
        exact_keys(
            validator,
            {"effective_balance", "slashed", "activation_epoch", "exit_epoch"},
            f"{path}.validators[{index}]",
        )
        integer(validator["effective_balance"], f"{path}.validators[{index}].effective_balance")
        if not isinstance(validator["slashed"], bool):
            fail(f"{path}.validators[{index}].slashed: expected boolean")
        integer(validator["activation_epoch"], f"{path}.validators[{index}].activation_epoch")
        integer(validator["exit_epoch"], f"{path}.validators[{index}].exit_epoch")
    checkpoint(value["current_justified_checkpoint"], f"{path}.current_justified_checkpoint")
    checkpoint(value["finalized_checkpoint"], f"{path}.finalized_checkpoint")


def store(value: Any, path: str) -> None:
    exact_keys(value, STORE_KEYS, path)
    for name in (
        "time",
        "genesis_time",
    ):
        integer(value[name], f"{path}.{name}")
    for name in (
        "justified_checkpoint",
        "finalized_checkpoint",
        "unrealized_justified_checkpoint",
        "unrealized_finalized_checkpoint",
    ):
        checkpoint(value[name], f"{path}.{name}")
    root(value["proposer_boost_root"], f"{path}.proposer_boost_root")
    if not isinstance(value["equivocating_indices"], list):
        fail(f"{path}.equivocating_indices: expected list")
    for index, item in enumerate(value["equivocating_indices"]):
        integer(item, f"{path}.equivocating_indices[{index}]")

    for index, block in enumerate(value["blocks"]):
        exact_keys(block, {"root", "slot", "parent_root"}, f"{path}.blocks[{index}]")
        root(block["root"], f"{path}.blocks[{index}].root")
        integer(block["slot"], f"{path}.blocks[{index}].slot")
        root(block["parent_root"], f"{path}.blocks[{index}].parent_root")
    for name in ("block_states", "checkpoint_states"):
        if not isinstance(value[name], list):
            fail(f"{path}.{name}: expected list")
        for index, item in enumerate(value[name]):
            if name == "block_states":
                exact_keys(item, {"root", "state"}, f"{path}.{name}[{index}]")
                root(item["root"], f"{path}.{name}[{index}].root")
            else:
                exact_keys(item, {"checkpoint", "state"}, f"{path}.{name}[{index}]")
                checkpoint(item["checkpoint"], f"{path}.{name}[{index}].checkpoint")
            state(item["state"], f"{path}.{name}[{index}].state")
    for index, item in enumerate(value["block_timeliness"]):
        exact_keys(item, {"root", "timely"}, f"{path}.block_timeliness[{index}]")
        root(item["root"], f"{path}.block_timeliness[{index}].root")
        if not isinstance(item["timely"], bool):
            fail(f"{path}.block_timeliness[{index}].timely: expected boolean")
    for index, item in enumerate(value["latest_messages"]):
        exact_keys(item, {"index", "epoch", "root"}, f"{path}.latest_messages[{index}]")
        integer(item["index"], f"{path}.latest_messages[{index}].index")
        integer(item["epoch"], f"{path}.latest_messages[{index}].epoch")
        root(item["root"], f"{path}.latest_messages[{index}].root")
    for index, item in enumerate(value["unrealized_justifications"]):
        exact_keys(item, {"root", "checkpoint"}, f"{path}.unrealized_justifications[{index}]")
        root(item["root"], f"{path}.unrealized_justifications[{index}].root")
        checkpoint(item["checkpoint"], f"{path}.unrealized_justifications[{index}].checkpoint")


def fcr(value: Any, path: str, schema: int) -> None:
    keys = FCR_KEYS | {"current_epoch_greatest_unrealized_checkpoint"} if schema == 2 else FCR_KEYS
    exact_keys(value, keys, path)

    for name, item in value.items():
        if name.endswith("checkpoint"):
            checkpoint(item, f"{path}.{name}")
        else:
            root(item, f"{path}.{name}")


def external(value: Any, function: str, path: str) -> None:
    if not isinstance(value, list):
        fail(f"{path}: expected list")
    for index, item in enumerate(value):
        item_path = f"{path}[{index}]"
        if function == "get_beacon_committee":
            exact_keys(item, {"state", "slot", "index", "result"}, item_path)
            state(item["state"], f"{item_path}.state")
            integer(item["slot"], f"{item_path}.slot")
            integer(item["index"], f"{item_path}.index")
            if not isinstance(item["result"], list):
                fail(f"{item_path}.result: expected list")
            for result_index, result in enumerate(item["result"]):
                integer(result, f"{item_path}.result[{result_index}]")
        elif function == "get_committee_count_per_slot":
            exact_keys(item, {"state", "epoch", "result"}, item_path)
            state(item["state"], f"{item_path}.state")
            integer(item["epoch"], f"{item_path}.epoch")
            integer(item["result"], f"{item_path}.result")
        elif function == "process_slots":
            exact_keys(item, {"state", "slot", "result"}, item_path)
            state(item["state"], f"{item_path}.state")
            integer(item["slot"], f"{item_path}.slot")
            state(item["result"], f"{item_path}.result")
        else:
            exact_keys(item, {"state", "result"}, item_path)
            state(item["state"], f"{item_path}.state")
            state(item["result"], f"{item_path}.result")


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {Path(sys.argv[0]).name} TRACE.jsonl", file=sys.stderr)
        return 2
    path = Path(sys.argv[1])
    records = 0
    tests: set[str] = set()
    states: set[str] = set()
    external_counts: Counter[str] = Counter()
    try:
        with path.open(encoding="utf-8") as handle:
            for line_number, line in enumerate(handle, 1):
                if not line.strip():
                    fail(f"line {line_number}: blank line")
                record = json.loads(line)
                exact_keys(
                    record,
                    {
                        "schema",
                        "test_id",
                        "fork",
                        "preset",
                        "call_index",
                        "config",
                        "store",
                        "fcr_before",
                        "fcr_after",
                        "externals",
                    },
                    f"line {line_number}",
                )
                if record["schema"] not in {1, 2}:

                    fail(f"line {line_number}: unsupported schema")
                if not isinstance(record["test_id"], str):
                    fail(f"line {line_number}.test_id: expected string")
                if not isinstance(record["fork"], str) or not isinstance(record["preset"], str):
                    fail(f"line {line_number}: fork and preset must be strings")
                integer(record["call_index"], f"line {line_number}.call_index")
                exact_keys(record["config"], CONFIG_KEYS, f"line {line_number}.config")
                for name, item in record["config"].items():
                    integer(item, f"line {line_number}.config.{name}")
                store(record["store"], f"line {line_number}.store")
                fcr(record["fcr_before"], f"line {line_number}.fcr_before", record["schema"])
                fcr(record["fcr_after"], f"line {line_number}.fcr_after", record["schema"])

                exact_keys(record["externals"], EXTERNAL_KEYS, f"line {line_number}.externals")
                for function in EXTERNAL_KEYS:
                    external(record["externals"][function], function, f"line {line_number}.externals.{function}")
                    external_counts[function] += len(record["externals"][function])
                records += 1
                tests.add(record["test_id"])
                for item in record["store"]["block_states"]:
                    states.add(json.dumps(item["state"], sort_keys=True, separators=(",", ":")))
                for item in record["store"]["checkpoint_states"]:
                    states.add(json.dumps(item["state"], sort_keys=True, separators=(",", ":")))
                for function in EXTERNAL_KEYS:
                    for item in record["externals"][function]:
                        states.add(json.dumps(item["state"], sort_keys=True, separators=(",", ":")))
                        if function in {"process_slots", "process_justification_and_finalization"}:
                            states.add(json.dumps(item["result"], sort_keys=True, separators=(",", ":")))
    except (OSError, json.JSONDecodeError, ValueError) as error:
        print(f"check_trace: FAIL: {error}", file=sys.stderr)
        return 1

    print(f"records={records}")
    print(f"tests={len(tests)}")
    print(f"distinct_states={len(states)}")
    for function in sorted(EXTERNAL_KEYS):
        print(f"externals.{function}={external_counts[function]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
