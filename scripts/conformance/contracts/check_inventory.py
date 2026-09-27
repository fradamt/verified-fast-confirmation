#!/usr/bin/env python3
"""Check the premise and input field inventory and run pinned contract probes."""
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
INTERNAL_PREMISES = ROOT / "FastConfirmationInternal" / "Premises"
# Internal FFG interpretation records that the pyspec projection runner probes
# for the canonical interpretation of the concrete bridge.
PROJECTED = ("AcceptedBlockFFGState", "FFGStateReadAgreement",
             "FFGStateAndCheckpointReadAgreement", "ScheduledFFGInterpretation",
             "EpochCheckpointProjectionLaws", "IncludedLinkCheckpointAgreement")


STRUCTURE = re.compile(
    r"(?:^|\n)structure\s+([A-Za-z_][\w.]*)[\s\S]*?\bwhere\n"
    r"([\s\S]*?)(?=\n(?:end|namespace|structure|/-!|section|def |abbrev |variable )|\Z)")


def declared_fields(path: Path) -> dict[str, set[str]]:
    """Map each structure name (last component) in a Lean file to its fields."""
    found: dict[str, set[str]] = {}
    for name, body in STRUCTURE.findall(path.read_text()):
        fields = found.setdefault(name.rsplit(".", 1)[-1], set())
        fields.update(re.findall(r"(?m)^  ([A-Za-z_][\w]*)\s*:", body))
    return found


def source_fields(reachable: set[str] | None = None,
                  folder: Path = PREMISES) -> dict[str, str]:
    """Regex scan: direct fields of the structures in `folder`, with their files."""
    fields = {}
    for path in sorted(folder.glob("*.lean")):
        for name, body in STRUCTURE.findall(path.read_text()):
            if reachable is not None and name not in reachable:
                continue
            for field in re.findall(r"(?m)^  ([A-Za-z_][\w]*)\s*:", body):
                key = f"{name}.{field}"
                if key in fields:
                    raise ValueError(f"duplicate Lean field: {key}")
                fields[key] = path.relative_to(ROOT).as_posix()
    return fields


def lean_rows(audit: str) -> tuple[dict[str, str], set[str]]:
    """Inventory keys of the Lean PF rows, with files, and the REC keys.

    A key is `<structure>.<field>`, with the last component of the structure
    name, or its last two components when two PF structures share the last one
    (for example `ConcreteBridge.Admissible` and `FFGSetup.Admissible`)."""
    declarations = {}
    for line in audit.splitlines():
        if line.startswith("PF\t"):
            _, module, declaration = line.split("\t")
            declarations[declaration] = module.replace(".", "/") + ".lean"
    structures = {declaration.rsplit(".", 1)[0] for declaration in declarations}
    last = {}
    for structure in structures:
        last.setdefault(structure.rsplit(".", 1)[-1], set()).add(structure)

    def key(declaration: str) -> str:
        structure, field = declaration.rsplit(".", 1)
        parts = structure.split(".")
        short = parts[-1] if len(last[parts[-1]]) == 1 else ".".join(parts[-2:])
        return f"{short}.{field}"

    keys = {key(declaration): file for declaration, file in declarations.items()}
    if len(keys) != len(declarations):
        raise ValueError("Lean PF rows do not have distinct inventory keys")
    records = {key(line.split("\t", 1)[1]) for line in audit.splitlines()
               if line.startswith("REC\t")}
    if not records <= keys.keys():
        raise ValueError(f"REC rows without PF rows: {sorted(records - keys.keys())}")
    return keys, records


def check_inventory(reachable_file: Path | None = None) -> dict[str, dict]:
    data = tomllib.loads((HERE / "inventory.toml").read_text())
    if data.get("version") != 2:
        raise ValueError("unknown inventory version")
    rows = data["field"]
    boundaries = data.get("boundary", [])
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
        if not labels or len(set(labels)) != len(labels) or any(label not in ("T", "E-scope", "E-network/behavior", "E-interpretation", "I", "definition", "record") for label in labels):
            raise ValueError(f"invalid class: {key}")
        if any(label in ("T", "definition", "record") for label in labels) and len(labels) != 1:
            raise ValueError(f"T, definition, and record cannot be mixed: {key}")
        if row["class"] == "T" and not row.get("test"):
            raise ValueError(f"missing test: {key}")
        if row["class"] != "T" and not row.get("reason"):
            raise ValueError(f"missing reason: {key}")
        # Every row names a field that its file declares.
        structure, field = key.rsplit(".", 1)
        path = ROOT / row["file"]
        if not path.is_file() or field not in declared_fields(path).get(
                structure.rsplit(".", 1)[-1], set()):
            raise ValueError(f"inventory row names no declared field: {key} in {row['file']}")
        inventory[key] = row
    # The regex scan of the Statements premise folder needs no Lean build.
    source = source_fields()
    missing = set(source) - set(inventory)
    misplaced = [k for k in source.keys() & inventory.keys() if source[k] != inventory[k]["file"]]
    if missing or misplaced:
        raise ValueError(f"premise fields without rows={sorted(missing)}, wrong file={sorted(misplaced)}")
    if reachable_file is not None:
        # The Lean rows are exact: every field of a claim-reachable premise
        # structure, and every proof-valued field of an input structure of the
        # claim, recursively (see scripts/StatementReachability.lean).
        audit = reachable_file.read_text()
        if "SR\tFastConfirmationStatements.Premises.ConcreteSafety\t" not in audit:
            raise ValueError("reachability audit has no safety premise root")
        lean_fields, records = lean_rows(audit)
        if not lean_fields:
            raise ValueError("Lean reachability audit has no premise fields")
        without_row = set(lean_fields) - set(inventory)
        stale = set(inventory) - set(lean_fields)
        wrong_file = [k for k in lean_fields.keys() & inventory.keys()
                      if lean_fields[k] != inventory[k]["file"]]
        if without_row or stale or wrong_file:
            raise ValueError(f"Lean fields without inventory rows={sorted(without_row)}, "
                             f"rows without Lean fields={sorted(stale)}, wrong file={sorted(wrong_file)}")
        classed = {k for k, row in inventory.items() if row["class"] == "record"}
        if classed != records:
            raise ValueError(f"record class differs from Lean record fields: {sorted(classed ^ records)}")
        lean_boundaries = {line.split("\t", 1)[1] for line in audit.splitlines()
                           if line.startswith("RB\t")}
        boundary_names = {"FastConfirmation.Spec." + row["path"] for row in boundaries}
        if lean_boundaries != boundary_names:
            raise ValueError(f"Lean boundary mismatch: {sorted(lean_boundaries ^ boundary_names)}")
    premise_rows = sum(row["file"].startswith("FastConfirmationStatements/Premises/")
                       for row in rows)
    counts = {klass: sum(klass in row["class"].split("+") for row in rows)
              for klass in ("T", "E-scope", "E-network/behavior", "E-interpretation", "I",
                            "definition", "record")}
    leaves = sum(row["class"] not in ("definition", "record") for row in rows)
    print(f"contract inventory passed: {len(rows)} fields ({premise_rows} Statements premise "
          f"fields, {len(rows) - premise_rows} Model input fields; {leaves} assumed leaves), "
          f"{len(boundaries)} outside boundaries"
          + ("" if reachable_file is None else ", Lean rows exact") + ": "
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
        bad_tests = [row['law'] for row in results if row['law'] in expected
                     and (row['status'] != 'PASS' or row['cases'] <= 0)]
        if bad_tests:
            raise ValueError(f"T tests did not pass positive case counts: {sorted(bad_tests)}")
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
        expected_runs = {'full-epoch-6': 49, 'review-slot-16': 17,
                         'late-two-thirds': 25, 'skipped-epoch': 25,
                         'two-forks': 33, 'later-anchor-out-of-scope': 1,
                         'two-step-finality-epoch-1-out-of-scope': 45,
                         'two-step-finality': 45} if args.full else {
                             'full-fast': 18, 'review-slot-16': 17}
        if {run['name']: run['blocks'] for run in projection['runs']} != expected_runs:
            raise ValueError('projection run set or accepted-block counts differ')
        projection_names = {row["field"] for row in projection["results"]}
        expected_projection = {row["path"] for row in inventory.values()
                               if row["path"].startswith("EventualCheckpointInclusion.")}
        expected_projection.update(key for key in source_fields(folder=INTERNAL_PREMISES)
                                   if key.split(".", 1)[0] in PROJECTED)
        expected_projection.update(("ImportedBlockFinalizationLag", "GenesisOrNormalizedAnchor",
                                    "RealizableBySlotRun", "HonestEarlierTargetVoteOnCarrierChain",
                                    "IncludedCheckpointEvidence.causal"))
        missing_projection = expected_projection - projection_names
        if missing_projection:
            raise ValueError(f"projection coverage missing={sorted(missing_projection)}")
        no_instances = {name for name in expected_projection if all(
            row['scope'] == 'no instances' for row in projection['results']
            if row['field'] == name)}
        allowed_no_instances = set() if args.full else {'AcceptedBlockFFGState.realized_justified_max'}
        if no_instances != allowed_no_instances:
            raise ValueError(f'projection aggregate case coverage differs: {sorted(no_instances)}')
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
