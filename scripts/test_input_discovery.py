#!/usr/bin/env python3
"""Check direct and aliased claim inputs, exact failures, and guard removal.

Usage: test_input_discovery.py --reachable-file <StatementReachability output>
"""
from __future__ import annotations

import argparse
import importlib.util
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = "FastConfirmationNestedFieldUse"


def probe(sort: str, route: str, *, reads_all: bool) -> str:
    alias = "def" if route == "definition" else "abbrev"
    field = "HiddenAlias" if route in ("field", "definition") else "HiddenData"
    binder = "InputAlias" if route == "binder" else "Input"
    proof = ("(fun (_ : True) (_ : True) (h : False) => False.elim h) "
             "scope.epoch_order p.nested.needed p.nested.unread" if reads_all else "p.nested.needed")
    return f"""module
public import Lean
@[expose] public section
namespace FastConfirmation.Spec
structure HiddenData : {sort} where
  needed : True
  unread : False
{alias} HiddenAlias := HiddenData
structure FixedFFGScope where
  epoch_order : True
structure Input : {sort} where
  nested : {field}
abbrev InputAlias := Input
def ConfirmedRootSafeFromNextSlot : Prop := {binder} → FixedFFGScope → True
theorem confirmed_root_safe_from_next_slot : ConfirmedRootSafeFromNextSlot :=
  fun p {"scope" if reads_all else "_"} => {proof}
end FastConfirmation.Spec
end
"""


def rejected(result: subprocess.CompletedProcess[str], diagnostic: str) -> None:
    output = result.stdout + result.stderr
    errors = [line.split("error: ", 1)[1] for line in output.splitlines() if "error: " in line]
    if result.returncode == 0 or errors != [diagnostic]:
        raise AssertionError(f"wrong field-use rejection: {output}")


def accepted(result: subprocess.CompletedProcess[str]) -> None:
    if result.returncode:
        raise AssertionError(f"positive control failed: {result.stdout}{result.stderr}")


def block(path: str) -> str:
    text = (ROOT / path).read_text()
    lines = text[text.index("-- BEGIN input structures"):
                 text.index("-- END input structures")].splitlines()
    while lines and lines[0].startswith("--"):
        lines.pop(0)
    return "\n".join(lines) + "\n"


def lean(folder: Path, name: str, source: str) -> subprocess.CompletedProcess[str]:
    (folder / name).write_text(source)
    return subprocess.run(
        ["lake", "env", "bash", "-c", 'export LEAN_PATH="$1:$LEAN_PATH"; cd "$1" && lean "$2"',
         "bash", str(folder), name], cwd=ROOT, capture_output=True, text=True, timeout=600)


def lean_probes() -> int:
    reachability = block("scripts/StatementReachability.lean")
    if reachability != block("scripts/PremiseFieldUse.lean"):
        raise AssertionError("the two input-structure blocks differ")
    source = (ROOT / "scripts/PremiseFieldUse.lean").read_text().replace(
        "import FastConfirmation\n", f"import {MODULE}\n", 1)
    guard = ('  unless failures.isEmpty do\n'
             '    throwError "premise or input fields that no proof reads: {failures.toList}"\n')
    assert source.count(guard) == 1
    mutant = source.replace(guard, '')
    diagnostic = ('premise or input fields that no proof reads: '
                  '[FastConfirmation.Spec.HiddenData.unread]')
    count = 0
    with tempfile.TemporaryDirectory(prefix="fcr-input-discovery-") as name:
        folder = Path(name)
        for sort in ("Prop", "Type"):
            for route in ("direct", "field", "binder", "definition"):
                for reads_all in (False, True):
                    (folder / f"{MODULE}.lean").write_text(probe(sort, route, reads_all=reads_all))
                    compiled = subprocess.run(
                        ["lake", "env", "bash", "-c", 'export LEAN_PATH="$1:$LEAN_PATH"; cd "$1" && '
                         f'lean -o {MODULE}.olean {MODULE}.lean', "bash", str(folder)],
                        cwd=ROOT, capture_output=True, text=True, timeout=600)
                    accepted(compiled)
                    result = lean(folder, "FieldUse.lean", source)
                    if reads_all:
                        accepted(result)
                        if any(line.startswith("UNREAD\t") for line in result.stdout.splitlines()):
                            raise AssertionError(f"positive proof did not read every field: {result.stdout}")
                        continue
                    rejected(result, diagnostic)
                    control = lean(folder, "WithoutGuard.lean", mutant)
                    accepted(control)
                    try:
                        rejected(control, diagnostic)
                    except AssertionError:
                        pass
                    else:
                        raise AssertionError("negative field test survived guard removal")
                    # Exercise the shared inventory-discovery block on the same
                    # compiled input. Type records also carry proof-valued fields.
                    runner = f"""import {MODULE}
import Lean
open Lean Elab Command
{reachability}
run_cmd do
  let env ← getEnv
  let inputs ← liftTermElabM <| inputStructures env
  for s in inputs do
    IO.println s!"INPUT {{s}}"
    for field in getStructureFields env s do
      let some info := env.find? (s ++ field) | continue
      if ← liftTermElabM <| isPropValued info.type then
        IO.println s!"PF {{s ++ field}}"
        if let some head ← liftTermElabM <| resultHead? info.type then
          if inputs.contains head then IO.println s!"REC {{s ++ field}}"
"""
                    result = lean(folder, "Discovery.lean", runner)
                    accepted(result)
                    rows = set(result.stdout.splitlines())
                    expected = {"PF FastConfirmation.Spec.HiddenData.needed",
                                "PF FastConfirmation.Spec.HiddenData.unread",
                                "INPUT FastConfirmation.Spec.Input",
                                "INPUT FastConfirmation.Spec.HiddenData"}
                    if sort == "Prop":
                        expected |= {"PF FastConfirmation.Spec.Input.nested",
                                     "REC FastConfirmation.Spec.Input.nested"}
                    if not expected <= rows:
                        raise AssertionError(f"{sort}/{route}: missing rows: {expected - rows}")
                    count += 1
                    print(f"input {sort}/{route}: exact rejection, discovery, guard removal", flush=True)
    return count


def inventory_probes(reachable: Path) -> int:
    path = ROOT / "scripts/conformance/contracts/check_inventory.py"
    spec = importlib.util.spec_from_file_location("check_inventory_probe", path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    original = (module.HERE / "inventory.toml").read_text()
    audit = reachable.read_text()
    extra = ("PF\tFastConfirmationStatements.Premises.ConcreteSafety\t"
             "FastConfirmation.Spec.HiddenPremises.unread\n")
    missing_row = original.replace(
        '[[field]]\npath = "Config.slots_per_epoch_pos"', '[[ignored]]\npath = "x"', 1)
    record_as_leaf = original.replace(
        'path = "ConcreteBridge.Admissible.setup"\n'
        'file = "FastConfirmationModel/Execution/ConcreteBridge.lean"\nclass = "record"',
        'path = "ConcreteBridge.Admissible.setup"\n'
        'file = "FastConfirmationModel/Execution/ConcreteBridge.lean"\nclass = "E-scope"', 1)
    cases = (
        ("missing Model leaf row", missing_row, audit,
         "Lean fields without inventory rows=['Config.slots_per_epoch_pos'], "
         "rows without Lean fields=[], wrong file=[]",
         "if without_row or stale or wrong_file:"),
        ("new nested leaf", original, audit + extra,
         "Lean fields without inventory rows=['HiddenPremises.unread'], "
         "rows without Lean fields=[], wrong file=[]",
         "if without_row or stale or wrong_file:"),
        ("record class changed", record_as_leaf, audit,
         "record class differs from Lean record fields: ['ConcreteBridge.Admissible.setup']",
         "if classed != records:"),
    )
    if missing_row == original or record_as_leaf == original:
        raise AssertionError("inventory probe did not change the inventory")
    with tempfile.TemporaryDirectory(prefix="fcr-inventory-negative-") as name:
        folder = Path(name)
        module.HERE = folder
        def verify(checker, expected: str) -> None:
            try:
                checker.check_inventory(folder / "reachable.txt")
            except ValueError as exc:
                if expected != str(exc):
                    raise AssertionError(f"wrong inventory rejection: {exc}") from exc
            else:
                raise AssertionError("inventory accepted the mutation")

        (folder / "inventory.toml").write_text(original)
        (folder / "reachable.txt").write_text(audit)
        module.check_inventory(folder / "reachable.txt")
        for label, inventory, rows, expected, guard in cases:
            (folder / "inventory.toml").write_text(inventory)
            (folder / "reachable.txt").write_text(rows)
            verify(module, expected)
            checker_source = path.read_text()
            assert checker_source.count(guard) == 1
            scratch = folder / "scripts/conformance/contracts/without_guard.py"
            scratch.parent.mkdir(parents=True, exist_ok=True)
            scratch.write_text(checker_source.replace(guard, "if False:  # removed target guard"))
            mutant_spec = importlib.util.spec_from_file_location("inventory_without_guard", scratch)
            mutant = importlib.util.module_from_spec(mutant_spec)
            assert mutant_spec.loader is not None
            mutant_spec.loader.exec_module(mutant)
            mutant.ROOT, mutant.HERE = module.ROOT, folder
            mutant.PREMISES = module.PREMISES
            mutant.INTERNAL_PREMISES = module.INTERNAL_PREMISES
            # Guard removal must accept the fixture. An unrelated error is a failure.
            mutant.check_inventory(folder / "reachable.txt")
            try:
                verify(mutant, expected)
            except AssertionError:
                pass
            else:
                raise AssertionError(f"{label}: negative test survived guard removal")
    return len(cases)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reachable-file", type=Path, required=True)
    args = parser.parse_args()
    if shutil.which("lake") is None:
        raise SystemExit("lake is required")
    fields = lean_probes()
    count = inventory_probes(args.reachable_file)
    print(f"input discovery tests passed: {fields + count} negatives; "
          f"{fields + count} guard-removal controls; {fields} positive field controls")


if __name__ == "__main__":
    main()
