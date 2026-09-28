#!/usr/bin/env python3
"""Run the production `scripts/Audit.lean` against two loaded-environment probes.

1. A scratch `Mathlib.olean` first on LEAN_PATH re-exports the review theorem
   and adds an opaque constant (the cf-audit shadow case). The audit must reject
   the import provenance.
2. A scratch Model module holds authored proofs that a source regex can miss:
   a quoted name, a `set_option ... in` prefix, a proof-valued definition and a
   proof-valued instance. The audit must name all four.

The second probe uses a scratch copy of the repository whose project build
folder holds hard links to the built object files, so the real build folder
is not changed. Run it after `lake build`.
"""
from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDIT = (ROOT / "scripts/Audit.lean").read_text()


def lean(cwd: Path, command: str, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["lake", "env", "bash", "-c", command, "bash", *args], cwd=cwd,
                          capture_output=True, text=True, timeout=900)


def expect_failure(result: subprocess.CompletedProcess[str], *expected: str) -> None:
    output = result.stdout + result.stderr
    if result.returncode == 0 or any(text not in output for text in expected):
        raise AssertionError(f"audit did not reject {expected}: {output[-2000:]}")


def compiled(result: subprocess.CompletedProcess[str], what: str) -> None:
    if result.returncode:
        raise AssertionError(f"could not compile {what}: {(result.stdout + result.stderr)[-2000:]}")


def shadow_package(folder: Path) -> None:
    shadow = folder / "shadow"
    shadow.mkdir()
    mathlib = ROOT / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib"
    (shadow / "Mathlib").symlink_to(mathlib.resolve(), target_is_directory=True)
    (shadow / "Mathlib.lean").write_text(
        "module\npublic import FastConfirmationProofs.ReviewTheorem\n"
        "@[expose] public section\nopaque auditExternal : Nat := 7\nend\n")
    (shadow / "AuditShadow.lean").write_text("import Mathlib\n" + AUDIT)
    compiled(lean(ROOT, 'export LEAN_PATH="$1:$LEAN_PATH"; cd "$1" && '
                  'lean -o Mathlib.olean Mathlib.lean', str(shadow)), "shadow Mathlib")
    check = lean(ROOT, 'export LEAN_PATH="$1:$LEAN_PATH"; lean "$1/AuditShadow.lean"', str(shadow))
    expect_failure(check, "import provenance failed", "root Mathlib is in more than one search path entry",
                   "Mathlib: resolves outside the project, toolchain, and pinned packages")


def link_tree(source: Path, target: Path) -> None:
    try:
        shutil.copytree(source, target, copy_function=os.link, symlinks=True)
    except OSError:
        shutil.rmtree(target, ignore_errors=True)
        shutil.copytree(source, target, symlinks=True)


def model_proofs(folder: Path) -> None:
    root = folder / "repo"
    shutil.copytree(ROOT, root, ignore=shutil.ignore_patterns(
        ".git", ".lake", ".source", "__pycache__"))
    (root / ".lake").mkdir()
    (root / ".lake/packages").symlink_to(ROOT / ".lake/packages")
    link_tree(ROOT / ".lake/build/lib/lean", root / ".lake/build/lib/lean")
    probe = root / "FastConfirmationModel/AuditProbe.lean"
    probe.write_text("""module
public import Mathlib.Basic.Logic.Basic
@[expose] public section
namespace FastConfirmation.Spec.AuditProbe
public theorem «cfAuditQuoted» : True := True.intro
set_option linter.unusedVariables false in public theorem auTSetOption : True := True.intro
public def auTPropDef : True := True.intro
public instance auTInstance : Fact True := ⟨True.intro⟩
end FastConfirmation.Spec.AuditProbe
end
""")
    output = root / ".lake/build/lib/lean/FastConfirmationModel/AuditProbe.olean"
    compiled(lean(root, 'lean -o "$1" FastConfirmationModel/AuditProbe.lean', str(output)),
             "the Model probe")
    audit = root / "scripts/Audit.lean"
    audit.write_text(AUDIT.replace("import FastConfirmation\n",
                                   "import FastConfirmation\nimport FastConfirmationModel.AuditProbe\n", 1))
    check = lean(root, "lean scripts/Audit.lean")
    expect_failure(check, "authored proofs in Model or Statements",
                   *(f"FastConfirmation.Spec.AuditProbe.{name}" for name in
                     ("cfAuditQuoted", "auTSetOption", "auTPropDef", "auTInstance")))


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="fcr-audit-negative-", dir=ROOT / ".lake") as folder:
        shadow_package(Path(folder))
        model_proofs(Path(folder))
    print("negative audit tests passed: shadow package module and 4 Model proofs rejected")


if __name__ == "__main__":
    main()
