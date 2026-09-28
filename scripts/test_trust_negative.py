#!/usr/bin/env python3
"""Run isolated rejection probes against the production source checks."""
from __future__ import annotations

import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def run(root: Path, script: str, expected: str) -> None:
    result = subprocess.run(["python3", f"scripts/{script}"], cwd=root,
                            capture_output=True, text=True, timeout=90)
    output = result.stdout + result.stderr
    if result.returncode == 0 or expected not in output:
        raise AssertionError(f"{script} did not reject {expected}: {output[:1200]}")


def altered(path: Path, addition: str, script: str, expected: str, root: Path) -> None:
    original = path.read_text()
    try:
        path.write_text(original + addition)
        run(root, script, expected)
    finally:
        path.write_text(original)


def imported(path: Path, module: str, root: Path, script: str = "check_imports.py",
             expected: str | None = None) -> None:
    original = path.read_text()
    try:
        path.write_text(original.replace("module\n", f"module\npublic import {module}\n", 1))
        run(root, script, expected or module)
    finally:
        path.write_text(original)


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="fcr-trust-negative-") as folder:
        root = Path(folder) / "repo"
        # Copy only the tracked files into a fresh index, as a clean checkout has them.
        listed = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT, check=True,
                                capture_output=True, text=True).stdout.split("\0")
        for name in filter(None, listed):
            (root / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, root / name)
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        subprocess.run(["git", "add", "-A"], cwd=root, check=True)
        (root / ".lake").mkdir()
        (root / ".lake/packages").symlink_to(ROOT / ".lake/packages")
        helper = root / "AuTReexport.lean"
        helper.write_text("module\npublic import FastConfirmationProofs.ReviewTheorem\n")
        imported(root / "FastConfirmationStatements.lean", "AuTReexport", root)
        helper.unlink()
        for name, body in (
            ("AuTOpaque", "opaque logical : Nat := 7\n"),
            ("AuTInstance", "instance : Inhabited Nat := ⟨7⟩\n"),
        ):
            helper = root / f"{name}.lean"
            helper.write_text("module\n" + body)
            imported(root / "FastConfirmationModel.lean", name, root)
            helper.unlink()
        # A local file with a package module name (the cf-audit shadow case).
        shadow = root / "Mathlib.lean"
        shadow.write_text("module\npublic import FastConfirmationProofs.ReviewTheorem\n"
                          "@[expose] public section\nopaque auditExternal : Nat := 7\nend\n")
        statements = root / "FastConfirmationStatements.lean"
        imported(statements, "Mathlib", root, expected="Mathlib.lean: Lean file outside")
        imported(statements, "Mathlib", root, "check_review_boundary.py",
                 "-> Mathlib names a local file")
        shadow.unlink()
        # An object file whose root name shadows a pinned package on the search path.
        build = root / ".lake/build/lib/lean"
        build.mkdir(parents=True)
        (build / "Mathlib.olean").write_bytes(b"")
        imported(statements, "Mathlib", root,
                 expected="root name in more than one search path entry")
        shutil.rmtree(root / ".lake/build")
        # Authored proofs in Model: the comment gap, a quoted name, a command
        # prefix, and an `example`, which leaves no declaration.
        for addition, expected in (
            ("public theorem /- gap -/ auTUndetected : True := True.intro", "`theorem` keyword"),
            ("public theorem «cfAuditQuoted» : True := True.intro", "`theorem` keyword"),
            ("set_option linter.unusedVariables false in public theorem auTSetOption : "
             "True := True.intro", "`theorem` keyword"),
            ("example : True := True.intro", "`example` keyword"),
        ):
            altered(root / "FastConfirmationModel/Spec/Config.lean", f"\n{addition}\n",
                    "check_imports.py", expected, root)
        altered(root / "README.md", "\nAudit probe: `NoSuchRecord.synchrony`.\n",
                "check_doc_names.py", "NoSuchRecord.synchrony", root)
        altered(root / "docs/SPEC_MAP.md",
                "\n```text\n│ `NoSuchRecord.synchrony` │\n```\n",
                "check_doc_names.py", "NoSuchRecord.synchrony", root)
        # An untracked local file must not resolve a documented path.
        untracked = root / "docs/history/untracked-note.md"
        untracked.parent.mkdir()
        untracked.write_text("local note\n")
        altered(root / "README.md", "\nAudit probe: `docs/history/untracked-note.md`.\n",
                "check_doc_names.py", "unresolved `docs/history/untracked-note.md`", root)
        shutil.rmtree(untracked.parent)
        config = root / "FastConfirmationModel/Spec/Config.lean"
        readme = root / "README.md"
        old_config, old_readme = config.read_text(), readme.read_text()
        try:
            config.write_text(old_config +
                              "\n/-\nnamespace NoSuchRecord\ndef synchrony : True := True.intro\nend NoSuchRecord\n-/\n")
            readme.write_text(old_readme + "\nAudit probe: `NoSuchRecord.synchrony`.\n")
            run(root, "check_doc_names.py", "NoSuchRecord.synchrony")
        finally:
            config.write_text(old_config)
            readme.write_text(old_readme)
    print("negative trust source tests passed: 14 mutations rejected")


if __name__ == "__main__":
    main()
