#!/usr/bin/env python3
"""Check that changed spec text and stale generated Gloas code fail the source audit."""
from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PIN = "13f391516352f61b3ac5dcaae5be1884d104f86a"


def run(repo: Path, expected: str) -> None:
    result = subprocess.run(["python3", str(ROOT / "scripts/check_consensus_source.py"),
                             "--repo", str(repo)], capture_output=True, text=True,
                            timeout=360)
    if result.returncode == 0 or expected not in result.stderr:
        raise AssertionError(f"source audit did not reject {expected}: {result.stderr[:1000]}")


def main() -> None:
    source = Path(os.environ.get("CONSENSUS_SPECS_REPO", ROOT.parent / "consensus-specs"))
    if not (source / ".venv/bin/python").is_file():
        raise SystemExit(f"pinned pyspec interpreter is required: {source}")
    with tempfile.TemporaryDirectory(prefix="fcr-source-negative-") as folder:
        repo = Path(folder) / "spec"
        subprocess.run(["git", "clone", "--quiet", "--shared", str(source), str(repo)],
                       check=True, timeout=120)
        subprocess.run(["git", "-C", str(repo), "checkout", "--quiet", PIN],
                       check=True, timeout=60)
        path = repo / "presets/minimal/phase0.yaml"
        original = path.read_bytes()
        path.write_bytes(original + b"\n# trust negative test\n")
        run(repo, "source tree is dirty")
        path.write_bytes(original)
        (repo / ".venv").symlink_to(source / ".venv", target_is_directory=True)
        output = repo / "tests/core/pyspec/eth_consensus_specs/gloas"
        output.mkdir(parents=True, exist_ok=True)
        for preset in ("minimal", "mainnet"):
            shutil.copy2(source / "tests/core/pyspec/eth_consensus_specs/gloas" / f"{preset}.py",
                         output / f"{preset}.py")
        with (output / "minimal.py").open("ab") as file:
            file.write(b"\n# stale trust negative test\n")
        run(repo, "stale generated pyspec")
    print("negative source tests passed: dirty source and stale pyspec rejected")


if __name__ == "__main__":
    main()
