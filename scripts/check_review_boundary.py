#!/usr/bin/env python3
"""Check the parsed import closure of the safety Statements review library.

Every edge of the closure is kept. A project edge must stay in Model or
Statements. A non-project edge must resolve, on the Lake search path, to the
toolchain or to a pinned package with a tracked source file (see
`check_imports.Resolver`). Without the pinned packages (the fast CI job has no
Lake checkout) the script cannot give that proof: it then only rejects local
files that supply the module name, and it names the unresolved edges. Pass
`--require-resolution` to make that case fail.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_imports import ROOT, Resolver, is_project, local_lean_files  # noqa: E402

ENTRY = "FastConfirmationStatements"
ALLOWED = ("FastConfirmationModel", "FastConfirmationStatements")


def allowed(name: str) -> bool:
    return any(name == root or name.startswith(root + ".") for root in ALLOWED)


def self_test() -> None:
    for name in ("FastConfirmationInternal.ProofVocabulary.Vocabulary",
                 "FastConfirmationProofs.ReviewTheorem",
                 "FastConfirmationWitnesses.Index"):
        assert not allowed(name), name
    for name in ("FastConfirmationModel", "FastConfirmationModel.Execution.Stake",
                 "FastConfirmationStatements", "FastConfirmationStatements.Review"):
        assert allowed(name), name
    for name in ("Mathlib", "AuTReexport", "FastConfirmationProofsX"):
        assert not allowed(name), name
    print("review boundary self-test passed")


def packages_present() -> bool:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    return all((ROOT / ".lake" / "packages" / package["name"]).is_dir()
               for package in manifest["packages"])


def main() -> int:
    args = sys.argv[1:]
    if args == ["--self-test"]:
        self_test()
        return 0
    require = args == ["--require-resolution"]
    if args and not require:
        print("usage: check_review_boundary.py [--self-test | --require-resolution]",
              file=sys.stderr)
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
        graph[name] = {row["module"] for row in entry["result"]["imports"]}
    local = {".".join(Path(path).with_suffix("").parts) for path in local_lean_files()}
    resolver = Resolver() if packages_present() else None
    if resolver is None and require:
        raise RuntimeError("pinned packages are absent; external edges cannot be resolved")
    seen: set[str] = set()
    external: set[str] = set()
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
        for dep in graph[name] - seen:
            if is_project(dep) or dep.startswith("FastConfirmation"):
                pending.append(dep)
                continue
            if dep in local:
                raise RuntimeError(f"review closure edge {name} -> {dep} names a local file")
            if resolver is not None and resolver.origin(dep) == "project":
                raise RuntimeError(f"review closure edge {name} -> {dep} is not external")
            external.add(dep)
    unlisted = {name for name in modules if name == ENTRY or
                name.startswith(ENTRY + ".")} - seen
    if unlisted:
        raise RuntimeError(f"Statements modules outside review closure: {sorted(unlisted)}")
    if resolver is None:
        print(f"review boundary passed: {len(seen)} local modules; {len(external)} external "
              "imports NOT RESOLVED (pinned packages absent; full validation resolves them)")
    else:
        print(f"review boundary passed: {len(seen)} local modules; {len(external)} external "
              "imports resolved to the toolchain or pinned packages")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as exc:
        raise SystemExit(f"review boundary failed: {exc}")
