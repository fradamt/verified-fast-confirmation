#!/usr/bin/env python3
"""Negative tests for the discovery of claim inputs and their inventory rows.

1. The cf-audit N2 probe: a scratch claim whose premise record holds a new
   nested record with an unread `False` field. The production
   `scripts/PremiseFieldUse.lean` must reject the unread field, and the input
   block of `scripts/StatementReachability.lean` must find the nested fields
   and mark the container as a record.
2. The inventory (cf-audit R2): with the real Lean rows, a missing Model leaf
   row, an extra nested leaf, and a changed record class must each fail
   `check_inventory.py`.

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
PROBE = f"""module
public import Lean
@[expose] public section
namespace FastConfirmation.Spec
structure HiddenPremises : Prop where
  needed : True
  unread : False
namespace ConcreteFFG.ConcreteBridge
structure SafetyPremises : Prop where
  nested : HiddenPremises
end ConcreteFFG.ConcreteBridge
def ConfirmedRootSafeFromNextSlot : Prop := ConcreteFFG.ConcreteBridge.SafetyPremises → True
theorem confirmed_root_safe_from_next_slot : ConfirmedRootSafeFromNextSlot :=
  fun p => p.nested.needed
end FastConfirmation.Spec
end
"""


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


def lean_probes() -> None:
    reachability = block("scripts/StatementReachability.lean")
    if reachability != block("scripts/PremiseFieldUse.lean"):
        raise AssertionError("the two input-structure blocks differ")
    with tempfile.TemporaryDirectory(prefix="fcr-input-discovery-") as name:
        folder = Path(name)
        (folder / f"{MODULE}.lean").write_text(PROBE)
        compiled = subprocess.run(
            ["lake", "env", "bash", "-c", 'export LEAN_PATH="$1:$LEAN_PATH"; cd "$1" && '
             f'lean -o {MODULE}.olean {MODULE}.lean', "bash", str(folder)],
            cwd=ROOT, capture_output=True, text=True, timeout=600)
        if compiled.returncode:
            raise AssertionError(f"probe did not compile: {compiled.stdout}{compiled.stderr}")
        source = (ROOT / "scripts/PremiseFieldUse.lean").read_text().replace(
            "import FastConfirmation\n", f"import {MODULE}\n", 1)
        result = lean(folder, "FieldUse.lean", source)
        output = result.stdout + result.stderr
        if result.returncode == 0 or "FastConfirmation.Spec.HiddenPremises.unread" not in output:
            raise AssertionError(f"field use accepted the unread nested field: {output[-1500:]}")
        runner = f"""import {MODULE}
import Lean
open Lean Elab Command
{reachability}
run_cmd do
  let env ← getEnv
  let inputs ← liftTermElabM <| inputStructures env
  for s in inputs do
    for field in getStructureFields env s do
      let some info := env.find? (s ++ field) | continue
      if ← liftTermElabM <| isPropValued info.type then
        IO.println s!"PF {{s ++ field}}"
        if let some head ← liftTermElabM <| resultHead? info.type then
          if inputs.contains head then IO.println s!"REC {{s ++ field}}"
"""
        result = lean(folder, "Discovery.lean", runner)
        rows = set((result.stdout + result.stderr).splitlines())
        expected = {"PF FastConfirmation.Spec.HiddenPremises.needed",
                    "PF FastConfirmation.Spec.HiddenPremises.unread",
                    "PF FastConfirmation.Spec.ConcreteFFG.ConcreteBridge.SafetyPremises.nested",
                    "REC FastConfirmation.Spec.ConcreteFFG.ConcreteBridge.SafetyPremises.nested"}
        if result.returncode or not expected <= rows:
            raise AssertionError(f"discovery missed the nested record: {sorted(rows)[-20:]}")


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
         "Lean fields without inventory rows=['Config.slots_per_epoch_pos']"),
        ("new nested leaf", original, audit + extra,
         "Lean fields without inventory rows=['HiddenPremises.unread']"),
        ("record class changed", record_as_leaf, audit,
         "record class differs from Lean record fields: ['ConcreteBridge.Admissible.setup']"),
    )
    if missing_row == original or record_as_leaf == original:
        raise AssertionError("inventory probe did not change the inventory")
    with tempfile.TemporaryDirectory(prefix="fcr-inventory-negative-") as name:
        folder = Path(name)
        module.HERE = folder
        for label, inventory, rows, expected in cases:
            (folder / "inventory.toml").write_text(inventory)
            (folder / "reachable.txt").write_text(rows)
            try:
                module.check_inventory(folder / "reachable.txt")
            except ValueError as exc:
                if expected not in str(exc):
                    raise AssertionError(f"{label}: wrong rejection: {exc}") from exc
            else:
                raise AssertionError(f"inventory accepted the {label}")
    return len(cases)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reachable-file", type=Path, required=True)
    args = parser.parse_args()
    if shutil.which("lake") is None:
        raise SystemExit("lake is required")
    lean_probes()
    count = inventory_probes(args.reachable_file)
    print(f"input discovery tests passed: nested unread field rejected and discovered; "
          f"{count} inventory mutations rejected")


if __name__ == "__main__":
    main()
