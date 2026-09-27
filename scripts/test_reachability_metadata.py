#!/usr/bin/env python3
"""Check authored generated-looking names with the production classifier."""
from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
text = (ROOT / "scripts/StatementReachability.lean").read_text()
classifier = "private def isSourceDeclaration" + text.split("private def isSourceDeclaration", 1)[1].split("\nrun_cmd do", 1)[0]

with tempfile.TemporaryDirectory(prefix="fcr-reachability-negative-") as folder:
    temp = Path(folder)
    (temp / "ReachabilitySource.lean").write_text("""module
public import Lean.DeclarationRange
public section
namespace Hidden
def _sizeOfHidden : Prop := False
def casesOn : Prop := False
end Hidden
""")
    (temp / "ReachabilityProbe.lean").write_text("""import ReachabilitySource
import Lean.DeclarationRange
import Lean.Elab.Command
open Lean Elab Command
""" + classifier + """
run_cmd do
  let env ← getEnv
  for name in [``Hidden._sizeOfHidden, ``Hidden.casesOn] do
    unless ← isSourceDeclaration env name do
      throwError "authored generated-looking declaration was omitted: {name}"
  IO.println "REACHABILITY_METADATA_NEGATIVE_TESTS 2"
""")
    command = '''cd "$1"; export LEAN_PATH="$1:${LEAN_PATH:-}"; lean -o ReachabilitySource.olean ReachabilitySource.lean && lean ReachabilityProbe.lean'''
    result = subprocess.run(["lake", "env", "bash", "-c", command, "bash", str(temp)],
                            cwd=ROOT, capture_output=True, text=True, timeout=120)
    if result.returncode or "REACHABILITY_METADATA_NEGATIVE_TESTS 2" not in result.stdout:
        raise SystemExit(result.stdout + result.stderr)
print("negative reachability tests passed: 2 authored names retained")
