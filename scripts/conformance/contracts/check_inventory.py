#!/usr/bin/env python3
"""Check claim-reachable premise fields and run pinned contract probes."""
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


def source_fields(reachable: set[str] | None = None) -> dict[str, str]:
    fields = {}
    for path in sorted(PREMISES.glob("*.lean")):
        source = path.read_text()
        for name, body in re.findall(
            r"(?:^|\n)structure\s+([A-Za-z_][\w]*)[\s\S]*?\bwhere\n"
            r"([\s\S]*?)(?=\n(?:end|namespace|structure|/-!|section|def |abbrev |variable )|\Z)",
            source,
        ):
            if reachable is not None and name not in reachable:
                continue
            for field in re.findall(r"(?m)^  ([A-Za-z_][\w]*)\s*:", body):
                key = f"{name}.{field}"
                if key in fields:
                    raise ValueError(f"duplicate Lean field: {key}")
                fields[key] = path.name
    return fields


def check_inventory(reachable_file: Path | None = None) -> dict[str, dict]:
    data = tomllib.loads((HERE / "inventory.toml").read_text())
    if data.get("version") != 1:
        raise ValueError("unknown inventory version")
    rows = data["field"]
    boundaries = data.get("boundary", [])
    generated = data.get("generated", [])
    for row in boundaries:
        source = (ROOT / row["file"]).read_text()
        name = row["path"].rsplit(".", 1)[-1]
        if not re.search(r"\b" + re.escape(name) + r"\s*(?:\([^\n]*\))?\s*:\s*Prop\b", source) and not (name == "AnchorCommitsToState" and "AnchorCommitsToState : BeaconBlock Root → BeaconState Root → Prop" in source):
            raise ValueError(f"boundary declaration absent: {row['path']}")
        if row["class"] not in ("E-scope", "I") or not row.get("reason"):
            raise ValueError(f"boundary label absent: {row['path']}")
    inventory = {}
    for row in rows:
        key = row["path"]
        if key in inventory:
            raise ValueError(f"duplicate inventory entry: {key}")
        labels = row["class"].split("+")
        if not labels or len(set(labels)) != len(labels) or any(label not in ("T", "E-scope", "E-network/behavior", "E-interpretation", "I") for label in labels):
            raise ValueError(f"invalid class: {key}")
        if "T" in labels and len(labels) != 1:
            raise ValueError(f"T cannot be mixed: {key}")
        if row["class"] == "T" and not row.get("test"):
            raise ValueError(f"missing test: {key}")
        if row["class"] != "T" and not row.get("reason"):
            raise ValueError(f"missing reason: {key}")
        inventory[key] = row
    reachable = None
    if reachable_file is not None:
        audit = reachable_file.read_text()
        reachable = {line.split("\t")[-1].rsplit(".", 1)[-1]
                     for line in audit.splitlines() if line.startswith("SR\t")}
        if not reachable or "NextSlotSafetyPremises" not in reachable:
            raise ValueError("reachability audit has no safety premise root")
    source = source_fields(reachable)
    if reachable_file is not None:
        audit = reachable_file.read_text()
        lean_fields = {}
        for line in audit.splitlines():
            if line.startswith("PF\t"):
                _, module, declaration = line.split("\t")
                parts = declaration.split(".")
                lean_fields[".".join(parts[-2:])] = module.split(".")[-1] + ".lean"
        if not lean_fields:
            raise ValueError("Lean reachability audit has no premise fields")
        generated_fields = {row["path"]: row for row in generated}
        lean_only = set(lean_fields) - set(source)
        source_only = set(source) - set(lean_fields)
        if lean_only != set(generated_fields) or source_only:
            raise ValueError(f"Lean/source field mismatch: Lean-only={sorted(lean_only)}, source-only={sorted(source_only)}, classified generated={sorted(generated_fields)}")
        for key, row in generated_fields.items():
            if lean_fields[key] != row["file"] or row["class"] != "E-interpretation" or not row.get("reason"):
                raise ValueError(f"generated field metadata invalid: {key}")
        lean_boundaries = {line.split("\t", 1)[1] for line in audit.splitlines()
                           if line.startswith("RB\t")}
        boundary_names = {"FastConfirmation.Spec." + row["path"] for row in boundaries}
        if lean_boundaries != boundary_names:
            raise ValueError(f"Lean boundary mismatch: {sorted(lean_boundaries ^ boundary_names)}")
    missing = set(source) - set(inventory)
    stale = set(inventory) - set(source)
    misplaced = [k for k in source.keys() & inventory.keys() if source[k] != inventory[k]["file"]]
    if missing or stale or misplaced:
        raise ValueError(f"missing={sorted(missing)}, stale={sorted(stale)}, wrong file={sorted(misplaced)}")
    active = [row for row in rows if row["path"] in source]
    counts = {klass: sum(klass in row["class"].split("+") for row in active)
              for klass in ("T", "E-scope", "E-network/behavior", "E-interpretation", "I")}
    print(f"contract inventory passed: {len(active)} authored fields, {len(generated)} inherited projections, {len(boundaries)} outside boundaries "
          + " / ".join(f"{klass} {count}" for klass, count in counts.items()))
    return inventory


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, help="Pinned consensus-specs checkout")
    ap.add_argument("--python", type=Path, help="Pinned checkout interpreter")
    ap.add_argument("--inventory-only", action="store_true")
    ap.add_argument("--reachable-file", type=Path, help="Lean claim-type reachability audit output")
    ap.add_argument("--full", action="store_true", help="Run all projection scenarios")
    ap.add_argument("--output", type=Path, help="Test JSON result path")
    args = ap.parse_args()
    inventory = check_inventory(args.reachable_file)
    if args.inventory_only:
        return 0
    if args.repo is None:
        raise ValueError("--repo is required for property tests")
    python = args.python or args.repo / ".venv/bin/python"
    if not python.is_file():
        raise ValueError(f"pyspec interpreter absent at {python}")
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
        projection_path = result_path.with_name(result_path.stem + "-projection.json")
        projection_command = [str(python), str(HERE / "projection/run.py"),
                              "--repo", str(args.repo), "--output", str(projection_path)]
        if args.full:
            projection_command.append("--full")
        projected = subprocess.run(projection_command, cwd=ROOT, check=False, timeout=280)
        if not projection_path.is_file():
            raise ValueError(f"projection runner produced no JSON: exit {projected.returncode}")
        projection = json.loads(projection_path.read_text())
        projection_names = {row["field"] for row in projection["results"]}
        expected_projection = {row["path"] for row in inventory.values()
                               if row["path"].startswith(("AcceptedBlockFFGState.",
                                   "FFGStateReadAgreement.", "FFGStateAndCheckpointReadAgreement.",
                                   "ScheduledFFGInterpretation.",
                                   "EventualCheckpointInclusion.", "EpochCheckpointProjectionLaws.",
                                   "IncludedLinkCheckpointAgreement."))}
        expected_projection.update(("ImportedBlockFinalizationLag", "GenesisOrNormalizedAnchor"))
        missing_projection = expected_projection - projection_names
        if missing_projection:
            raise ValueError(f"projection coverage missing={sorted(missing_projection)}")
        bad_runs = [run for run in projection["runs"] if run["handler_errors"]]
        if bad_runs:
            raise ValueError(f"projection handler errors: {bad_runs}")
        findings = sorted({row["field"] for row in projection["results"]
                           if row["status"] == "FAIL"})
        if findings:
            raise ValueError(f"unexcluded projection failures: {findings}")
        if projected.returncode:
            raise ValueError(f"projection runner failed: exit {projected.returncode}")
        print(f"contract tests passed: {len(names)} state probes; "
              f"{len(projection['results'])} projection checks; unexcluded failures=0")
        return 0
    finally:
        if temporary:
            result_path.unlink(missing_ok=True)
            result_path.with_name(result_path.stem + "-projection.json").unlink(missing_ok=True)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, tomllib.TOMLDecodeError) as exc:
        raise SystemExit(f"contract inventory failed: {exc}")
