#!/usr/bin/env python3
"""Check the pinned Python source locations and the concrete Lean inventory."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tomllib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
INVENTORY = Path(__file__).with_name("source_inventory.toml")
PIN = "13f391516352f61b3ac5dcaae5be1884d104f86a"
REQUIRED_FRAMES = {
    "process_inactivity_updates", "process_rewards_and_penalties",
    "process_registry_updates", "process_slashings", "process_eth1_data_reset",
    "process_pending_deposits", "process_pending_consolidations",
    "process_builder_pending_payments", "process_effective_balance_updates",
    "process_slashings_reset", "process_randao_mixes_reset",
    "process_historical_summaries_update", "process_sync_committee_updates",
    "process_proposer_lookahead", "process_ptc_window",
}


def check(repo: Path) -> None:
    data = tomllib.loads(INVENTORY.read_text())
    functions = data["function"]
    frames = data["frame"]
    if len(functions) != 34 or len(frames) != 15:
        raise ValueError(f"expected 34 functions and 15 frames; got {len(functions)}, {len(frames)}")
    names = [row["name"] for row in functions]
    if len(names) != len(set(names)):
        raise ValueError("duplicate Lean function")
    frame_names = [row["name"] for row in frames]
    if len(frame_names) != len(set(frame_names)):
        raise ValueError("duplicate Lean frame")
    if set(frame_names) != REQUIRED_FRAMES:
        raise ValueError(f"frame set differs: missing={sorted(REQUIRED_FRAMES - set(frame_names))}, "
                         f"extra={sorted(set(frame_names) - REQUIRED_FRAMES)}")
    if set(names) & set(frame_names):
        raise ValueError(f"function/frame overlap: {sorted(set(names) & set(frame_names))}")
    actual = subprocess.check_output(
        ["git", "-C", str(repo), "rev-parse", "HEAD"], text=True
    ).strip()
    if actual != PIN:
        raise ValueError(f"Python revision differs: {actual}")
    for row in [*functions, *frames]:
        source = (repo / row["python"]).read_text().splitlines()
        line = row["line"]
        if line < 1 or line > len(source) or not re.match(
            rf"^def {re.escape(row['name'])}\(", source[line - 1]
        ):
            raise ValueError(f"wrong Python location: {row['name']} {row['python']}:{line}")
        if "lean" in row:
            lean = (ROOT / row["lean"]).read_text()
            if not re.search(rf"^def {re.escape(row['name'])}\b", lean, re.M):
                raise ValueError(f"missing Lean function: {row['name']}")
            citation = f"{row['python']}:{line}"
            if citation not in lean and row["lean"].endswith("ConcreteTransition.lean"):
                raise ValueError(f"missing Python citation: {row['name']} {citation}")
        else:
            lean = (ROOT / "FastConfirmationModel/Spec/BeaconChain/ConcreteTransition.lean").read_text()
            if not re.search(rf"^def {re.escape(row['name'])}\b", lean, re.M):
                raise ValueError(f"missing frame function: {row['name']}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    args = parser.parse_args()
    try:
        check(args.repo)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        print(f"concrete source inventory failed: {exc}", file=sys.stderr)
        return 1
    print("concrete source inventory passed: 34 functions, 15 frames")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
