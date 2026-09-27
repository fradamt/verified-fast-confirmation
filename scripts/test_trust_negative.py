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


def imported(path: Path, module: str, root: Path) -> None:
    original = path.read_text()
    try:
        path.write_text(original.replace("module\n", f"module\npublic import {module}\n", 1))
        run(root, "check_imports.py", module)
    finally:
        path.write_text(original)


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="fcr-trust-negative-") as folder:
        root = Path(folder) / "repo"
        shutil.copytree(ROOT, root, ignore=shutil.ignore_patterns(".git", ".lake", "__pycache__"))
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
        altered(root / "FastConfirmationModel/Spec/Config.lean",
                "\npublic theorem /- gap -/ auTUndetected : True := True.intro\n",
                "check_imports.py", "auTUndetected", root)
        altered(root / "README.md", "\nAudit probe: `NoSuchRecord.synchrony`.\n",
                "check_doc_names.py", "NoSuchRecord.synchrony", root)
        altered(root / "docs/SPEC_MAP.md",
                "\n```text\n│ `NoSuchRecord.synchrony` │\n```\n",
                "check_doc_names.py", "NoSuchRecord.synchrony", root)
    print("negative trust source tests passed: 6 mutations rejected")


if __name__ == "__main__":
    main()
