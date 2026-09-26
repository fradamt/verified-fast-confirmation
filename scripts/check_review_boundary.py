#!/usr/bin/env python3
"""Check the parsed import closure of the safety Statements review library."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ENTRY = "FastConfirmationStatements"
ALLOWED = ("FastConfirmationModel", "FastConfirmationStatements")


def allowed(name: str) -> bool:
    return any(name == root or name.startswith(root + ".") for root in ALLOWED)


def self_test() -> None:
    for name in ("FastConfirmationInternal.ProofVocabulary.Vocabulary",
                 "FastConfirmationProofs.ReviewTheorem",
                 "FastConfirmationWitnesses.Index", "FastConfirmationPaper.Core"):
        assert not allowed(name), name
    for name in ("FastConfirmationModel", "FastConfirmationModel.Execution.Stake",
                 "FastConfirmationStatements", "FastConfirmationStatements.Review"):
        assert allowed(name), name
    print("review boundary self-test passed")


def main() -> int:
    if sys.argv[1:] == ["--self-test"]:
        self_test()
        return 0
    if sys.argv[1:]:
        print("usage: check_review_boundary.py [--self-test]", file=sys.stderr)
        return 2
    paths = [ROOT / f"{ENTRY}.lean", *sorted((ROOT / ENTRY).rglob("*.lean")),
             ROOT / "FastConfirmationModel.lean",
             *sorted((ROOT / "FastConfirmationModel").rglob("*.lean"))]
    modules = {".".join(path.relative_to(ROOT).with_suffix("").parts): path
               for path in paths}
    result = subprocess.run(["lean", "--deps-json",
                             *(str(path.relative_to(ROOT)) for path in paths)],
                            cwd=ROOT, capture_output=True, text=True, check=True)
    entries = json.loads(result.stdout)["imports"]
    if len(entries) != len(paths):
        raise RuntimeError("Lean returned an incomplete import graph")
    graph: dict[str, set[str]] = {}
    for name, entry in zip(modules, entries, strict=True):
        if entry.get("errors") or not isinstance(entry.get("result"), dict):
            raise RuntimeError(f"Lean import error in {name}: {entry.get('errors')}")
        graph[name] = {row["module"] for row in entry["result"]["imports"]
                       if row["module"].startswith("FastConfirmation")}
    seen: set[str] = set()
    pending = [ENTRY]
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        if not allowed(name):
            raise RuntimeError(f"review closure contains {name}")
        if name not in modules:
            raise RuntimeError(f"review closure has no source module {name}")
        pending.extend(graph[name] - seen)
    unlisted = {name for name in modules if name == ENTRY or
                name.startswith(ENTRY + ".")} - seen
    if unlisted:
        raise RuntimeError(f"Statements modules outside review closure: {sorted(unlisted)}")
    print(f"review boundary passed: {len(seen)} local modules")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.CalledProcessError) as exc:
        raise SystemExit(f"review boundary failed: {exc}")
