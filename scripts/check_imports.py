#!/usr/bin/env python3
"""Check the six-library import order with Lean's parsed dependency graph."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = tuple("FastConfirmation" + name for name in
             ("Model", "Statements", "Internal", "Proofs", "Witnesses"))
PAPER = "FastConfirmationPaper"
LIBRARIES = (*SPEC, PAPER)


def owner(module: str) -> str | None:
    return next((lib for lib in LIBRARIES
                 if module == lib or module.startswith(lib + ".")), None)


def closure(start: str, graph: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    pending = [start]
    while pending:
        current = pending.pop()
        if current not in seen:
            seen.add(current)
            pending.extend(graph.get(current, set()) - seen)
    return seen


def audit() -> tuple[int, list[str]]:
    paths = [ROOT / "FastConfirmation.lean"]
    for lib in LIBRARIES:
        paths.append(ROOT / f"{lib}.lean")
        folder = ROOT / lib
        if not folder.is_dir() or folder.is_symlink():
            raise RuntimeError(f"missing or symlinked library folder: {folder}")
        paths.extend(sorted(folder.rglob("*.lean")))
    if any(not path.is_file() or path.is_symlink() for path in paths):
        raise RuntimeError("missing or symlinked project module")
    modules = {".".join(path.relative_to(ROOT).with_suffix("").parts): path
               for path in paths}
    if len(modules) != len(paths):
        raise RuntimeError("duplicate module path")
    relative = [str(path.relative_to(ROOT)) for path in paths]
    parsed = subprocess.run(["lean", "--deps-json", *relative], cwd=ROOT,
                            capture_output=True, text=True, timeout=60)
    if parsed.returncode:
        raise RuntimeError(f"Lean import parser failed: {parsed.stderr.strip()}")
    entries = json.loads(parsed.stdout)["imports"]
    if len(entries) != len(paths):
        raise RuntimeError("Lean returned an incomplete import graph")
    graph: dict[str, set[str]] = {}
    failures: list[str] = []
    for module, entry in zip(modules, entries, strict=True):
        if entry.get("errors") or not isinstance(entry.get("result"), dict):
            raise RuntimeError(f"{module}: Lean rejected the import header: {entry.get('errors')}")
        declarations = entry["result"].get("imports")
        if not isinstance(declarations, list):
            raise RuntimeError(f"{module}: Lean returned no imports")
        imports = {row["module"] for row in declarations
                   if row["module"].startswith("FastConfirmation")}
        missing = imports - modules.keys()
        if missing:
            failures.append(f"{module}: missing local imports {sorted(missing)}")
        graph[module] = imports & modules.keys()
        if module == "FastConfirmation":
            continue
        source = owner(module)
        if source is None:
            failures.append(f"{module}: outside the six libraries")
        for dep in sorted(imports):
            target = owner(dep)
            if target is None:
                failures.append(f"{module}: unknown project import {dep}")
            elif source == PAPER and target != PAPER:
                failures.append(f"{module}: Paper imports Spec side {dep}")
            elif source != PAPER and target == PAPER:
                failures.append(f"{module}: Spec side imports Paper {dep}")
            elif source in SPEC and target in SPEC and SPEC.index(target) > SPEC.index(source):
                failures.append(f"{module}: reverse library import {dep}")
    if graph["FastConfirmation"] != set(LIBRARIES):
        failures.append("root aggregate must import exactly the six library roots")
    for lib in LIBRARIES:
        owned = {module for module in modules if owner(module) == lib}
        orphaned = owned - closure(lib, graph)
        if orphaned:
            failures.append(f"{lib}: orphan modules {sorted(orphaned)}")
    orphaned = modules.keys() - closure("FastConfirmation", graph)
    if orphaned:
        failures.append(f"root aggregate orphan modules {sorted(orphaned)}")
    theorem_pattern = re.compile(
        r"^[ \t]*(?:@\[[^\n]*\][ \t]*)*"
        r"(?:(?:private|protected|public|noncomputable|partial|unsafe)[ \t]+)*"
        r"(?:theorem|lemma)\s+([\w'.₀-₉]+)", re.M)
    allowed = {
        ("FastConfirmationModel.Execution.ScheduledPrefixes", "processedCount_lt"),
        ("FastConfirmationStatements.Traces", "getLatestTraceResult_eq_getLatestConfirmed"),
    }
    found: set[tuple[str, str]] = set()
    for module, path in modules.items():
        if owner(module) not in SPEC[:2]:
            continue
        for match in theorem_pattern.finditer(path.read_text()):
            pair = (module, match.group(1))
            found.add(pair)
            if pair not in allowed:
                failures.append(f"{module}: theorem in Model or Statements: {pair[1]}")
    if found & allowed != allowed:
        failures.append(f"missing required proof terms: {sorted(allowed - found)}")
    return len(modules), failures


def main() -> int:
    try:
        count, failures = audit()
        if failures:
            raise RuntimeError("\n".join(failures))
    except (RuntimeError, OSError, ValueError, KeyError, subprocess.TimeoutExpired) as exc:
        print(f"import architecture audit failed:\n{exc}", file=sys.stderr)
        return 1
    print(f"import architecture audit passed: {count} modules, six libraries")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
