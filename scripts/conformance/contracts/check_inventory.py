#!/usr/bin/env python3
"""Check premise-field coverage and run the pinned contract probes."""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
PREMISES = ROOT / "FastConfirmationStatements" / "Premises"


def source_fields() -> dict[str, str]:
    fields = {}
    for path in sorted(PREMISES.glob("*.lean")):
        source = path.read_text()
        for name, body in re.findall(
            r"(?:^|\n)structure\s+([A-Za-z_][\w]*)[\s\S]*?\bwhere\n"
            r"([\s\S]*?)(?=\n(?:end|namespace|structure|/-!|section|def |abbrev |variable )|\Z)",
            source,
        ):
            for field in re.findall(r"(?m)^  ([A-Za-z_][\w]*)\s*:", body):
                key = f"{name}.{field}"
                if key in fields:
                    raise ValueError(f"duplicate Lean field: {key}")
                fields[key] = path.name
    return fields


def check_inventory() -> dict[str, dict]:
    data = tomllib.loads((HERE / "inventory.toml").read_text())
    if data.get("version") != 1:
        raise ValueError("unknown inventory version")
    rows = data["field"]
    inventory = {}
    for row in rows:
        key = row["path"]
        if key in inventory:
            raise ValueError(f"duplicate inventory entry: {key}")
        if row["class"] not in ("T", "E", "I"):
            raise ValueError(f"invalid class: {key}")
        if row["class"] == "T" and not row.get("test"):
            raise ValueError(f"missing test: {key}")
        if row["class"] != "T" and not row.get("reason"):
            raise ValueError(f"missing reason: {key}")
        inventory[key] = row
    source = source_fields()
    missing = set(source) - set(inventory)
    stale = {k for k in set(inventory) - set(source) if not inventory[k].get("optional", False)}
    misplaced = [k for k in source.keys() & inventory.keys() if source[k] != inventory[k]["file"]]
    if missing or stale or misplaced:
        raise ValueError(f"missing={sorted(missing)}, stale={sorted(stale)}, wrong file={sorted(misplaced)}")
    active = [row for row in rows if row["path"] in source]
    counts = {klass: sum(row["class"] == klass for row in active) for klass in ("T", "E", "I")}
    print(f"contract inventory passed: {len(active)} active fields (T {counts['T']} / E {counts['E']} / I {counts['I']})")
    return inventory


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, help="Pinned consensus-specs checkout")
    ap.add_argument("--python", type=Path, help="Pinned checkout interpreter")
    ap.add_argument("--inventory-only", action="store_true")
    ap.add_argument("--output", type=Path, help="Test JSON result path")
    args = ap.parse_args()
    inventory = check_inventory()
    if args.inventory_only:
        return 0
    if args.repo is None:
        raise ValueError("--repo is required for property tests")
    python = args.python or args.repo / ".venv/bin/python"
    if not python.is_file():
        print(f"contract tests skipped: pyspec interpreter absent at {python}")
        return 0
    result_path = args.output or ROOT / "scripts/conformance/contracts/.last-results.json"
    temporary = args.output is None
    try:
        command = [str(python), str(HERE / "test_contracts.py"), "--repo", str(args.repo), "--output", str(result_path)]
        completed = subprocess.run(command, cwd=ROOT, check=False)
        if not result_path.is_file():
            raise ValueError(f"contract runner produced no JSON: exit {completed.returncode}")
        results = json.loads(result_path.read_text())["results"]
        names = [row["law"] for row in results]
        expected = {row["test"] for row in inventory.values() if row["class"] == "T"}
        observed = set(names)
        missing = expected - observed
        if missing or len(names) != len(observed):
            raise ValueError(f"test coverage missing={sorted(missing)} duplicate={len(names)!=len(observed)}")
        if completed.returncode:
            raise ValueError(f"contract tests failed: exit {completed.returncode}")
        print(f"contract tests passed with recorded findings: {len(names)} laws")
        return 0
    finally:
        if temporary:
            result_path.unlink(missing_ok=True)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, tomllib.TOMLDecodeError) as exc:
        raise SystemExit(f"contract inventory failed: {exc}")
