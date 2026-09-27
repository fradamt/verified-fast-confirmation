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


def trace(repo: Path, out: Path, label: str) -> None:
    result = subprocess.run(["bash", str(ROOT / "scripts/conformance/run.sh"), str(repo),
                             "gloas", "minimal", str(out)], capture_output=True, text=True,
                            timeout=900)
    output = result.stdout + result.stderr
    if (result.returncode == 0 or "trace export refused" not in output or
            "consensus source audit failed" not in output or out.exists()):
        raise AssertionError(f"trace runner did not refuse the {label}: {output[-1000:]}")


def main() -> None:
    source = Path(os.environ.get("CONSENSUS_SPECS_REPO", ROOT.parent / "consensus-specs")).resolve()
    if not (source / ".venv/bin/python").is_file():
        raise SystemExit(f"pinned pyspec interpreter is required: {source}")
    with tempfile.TemporaryDirectory(prefix="fcr-source-negative-") as folder:
        repo = Path(folder) / "spec"
        subprocess.run(["git", "clone", "--quiet", "--shared", str(source), str(repo)],
                       check=True, timeout=120)
        subprocess.run(["git", "-c", "advice.detachedHead=false", "-C", str(repo),
                        "checkout", "--quiet", PIN],
                       check=True, timeout=60)
        path = repo / "presets/minimal/phase0.yaml"
        original = path.read_bytes()
        path.write_bytes(original + b"\n# trust negative test\n")
        run(repo, "source tree is dirty")
        path.write_bytes(original)
        (repo / ".venv").symlink_to(source / ".venv", target_is_directory=True)
        for fork in ("phase0", "altair", "bellatrix", "capella", "deneb",
                     "electra", "fulu", "gloas"):
            output = repo / "tests/core/pyspec/eth_consensus_specs" / fork
            output.mkdir(parents=True, exist_ok=True)
            for preset in ("minimal", "mainnet"):
                shutil.copy2(source / "tests/core/pyspec/eth_consensus_specs" / fork / f"{preset}.py",
                             output / f"{preset}.py")
        for fork in ("altair", "gloas"):
            module = repo / "tests/core/pyspec/eth_consensus_specs" / fork / "minimal.py"
            with module.open("ab") as file:
                file.write(b"\n# stale trust negative test\n")
            run(repo, "stale generated pyspec")
            shutil.copy2(source / "tests/core/pyspec/eth_consensus_specs" / fork / "minimal.py", module)
        # The standalone trace route (cf-audit R3): a dirty Altair source and a
        # stale generated Gloas module must stop it before any export.
        altair = repo / "specs/altair/beacon-chain.md"
        altair_text = altair.read_bytes()
        gloas = repo / "tests/core/pyspec/eth_consensus_specs/gloas/minimal.py"
        for label, path, addition in (
            ("dirty source", altair, b"\n<!-- cf audit dirty source -->\n"),
            ("stale generated pyspec", gloas, b"\n# cf audit stale generated module\n"),
        ):
            original_bytes = path.read_bytes()
            path.write_bytes(original_bytes + addition)
            trace(repo, Path(folder) / "trace.jsonl", label)
            path.write_bytes(original_bytes)
        if altair.read_bytes() != altair_text:
            raise AssertionError("scratch source was not restored")
    print("negative source tests passed: dirty source and two stale pyspec modules rejected; "
          "trace export refused for a dirty source and a stale generated module")


if __name__ == "__main__":
    main()
