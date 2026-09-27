#!/usr/bin/env python3
"""Check that the public witness fingerprint pins the witness definition closure.

The cf-audit probe (T-3): `finite_execution_satisfies_premises` has the bare
type `JointWitnessFacts`, so a hash of witness types alone does not change when
a field of that structure changes or disappears. This test compiles a small
witness module in five variants, runs the production fingerprint block of
`scripts/ReviewSurfaceShape.lean` on each, and requires five different values.
It also requires one value from the former type-only hash, which shows that the
variants reproduce the probe.
"""
from __future__ import annotations

import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SHAPE = (ROOT / "scripts/ReviewSurfaceShape.lean").read_text()
BLOCK = SHAPE[SHAPE.index("-- BEGIN witness fingerprint"):SHAPE.index("-- END witness fingerprint")]
MODULE = "FastConfirmationWitnessProbe"
NAMESPACE = "FastConfirmation.Spec.WitnessProbe"
BASE = f"""module
@[expose] public section
namespace {NAMESPACE}
structure JointWitnessFacts : Prop where
  premises : True
  public_safety_at_end : 1 = 1
def run : Nat := 3
theorem finite_execution_satisfies_premises : JointWitnessFacts := ⟨trivial, rfl⟩
theorem run_exercised : run = run := rfl
end {NAMESPACE}
end
"""
VARIANTS = {
    "base": BASE,
    "field removed": BASE.replace("  public_safety_at_end : 1 = 1\n", "")
                         .replace("⟨trivial, rfl⟩", "⟨trivial⟩"),
    "field type changed": BASE.replace("public_safety_at_end : 1 = 1",
                                       "public_safety_at_end : 2 = 2"),
    "field renamed": BASE.replace("public_safety_at_end", "safety_at_end"),
    "fixture body changed": BASE.replace("def run : Nat := 3", "def run : Nat := 4"),
}
RUNNER = f"""import {MODULE}
import Lean
open Lean Elab Command

{BLOCK}
run_cmd do
  let env ← getEnv
  let witnesses := #[`{NAMESPACE}.finite_execution_satisfies_premises,
    `{NAMESPACE}.run_exercised]
  let mut legacy : UInt64 := 0
  for name in witnesses do
    let some info := env.find? name | throwError "missing {{name}}"
    legacy := hash (legacy, name, info.type)
  let current ← ofExcept <| witnessFingerprint env witnesses
  IO.println s!"FINGERPRINT {{current}} LEGACY {{legacy}}"
"""


def fingerprint(folder: Path, source: str) -> tuple[str, str]:
    (folder / f"{MODULE}.lean").write_text(source)
    (folder / "Runner.lean").write_text(RUNNER)
    result = subprocess.run(
        ["lake", "env", "bash", "-c",
         'export LEAN_PATH="$1:$LEAN_PATH"; cd "$1" && '
         f'lean -o {MODULE}.olean {MODULE}.lean && lean Runner.lean', "bash", str(folder)],
        cwd=ROOT, capture_output=True, text=True, timeout=600)
    output = result.stdout + result.stderr
    match = re.search(r"FINGERPRINT (\d+) LEGACY (\d+)", output)
    if result.returncode or not match:
        raise AssertionError(f"fingerprint probe failed: {output[-2000:]}")
    return match.group(1), match.group(2)


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="fcr-witness-fingerprint-") as folder:
        values = {name: fingerprint(Path(folder), source) for name, source in VARIANTS.items()}
    current = {value[0] for value in values.values()}
    legacy = {value[1] for value in values.values()}
    if len(legacy) != 1:
        raise AssertionError(f"the variants no longer reproduce the type-only gap: {values}")
    if len(current) != len(VARIANTS):
        raise AssertionError(f"witness fingerprint missed a closure change: {values}")
    print(f"witness fingerprint test passed: {len(VARIANTS)} variants, "
          f"{len(current)} fingerprints, 1 type-only hash")


if __name__ == "__main__":
    main()
