#!/usr/bin/env python3
"""Check the five-library import order with Lean's parsed dependency graph."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = tuple("FastConfirmation" + name for name in
             ("Model", "Statements", "Internal", "Proofs", "Witnesses"))
LIBRARIES = SPEC


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


def external_roots() -> list[Path]:
    """Return source roots backed by the toolchain or a pinned Lake package."""
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    roots = [prefix / "src" / "lean"]
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        name, rev = package["name"], package.get("rev")
        folder = ROOT / ".lake" / "packages" / name
        if not rev or not folder.is_dir():
            raise RuntimeError(f"missing pinned package: {name}")
        head = subprocess.check_output(["git", "-C", str(folder), "rev-parse", "HEAD"],
                                       text=True).strip()
        if head != rev:
            raise RuntimeError(f"package {name} differs from lake-manifest.json")
        dirty = subprocess.check_output(
            ["git", "-C", str(folder), "status", "--porcelain", "--untracked-files=no"],
            text=True).strip()
        if dirty:
            raise RuntimeError(f"pinned package {name} has changed source files")
        roots.append(folder)
    return roots


def resolved_external(module: str, roots: list[Path]) -> bool:
    relative = Path(*module.split(".")).with_suffix(".lean")
    for root in roots:
        candidate = root / relative
        if (candidate.is_file() and not candidate.is_symlink() and
                candidate.resolve().is_relative_to(root.resolve())):
            return True
    return False


def without_comments(source: str) -> str:
    """Blank nested Lean comments, but retain line positions for the scan."""
    result = list(source)
    pos = 0
    depth = 0
    while pos < len(source):
        if source.startswith("/-", pos):
            depth += 1
            result[pos:pos + 2] = "  "
            pos += 2
        elif depth and source.startswith("-/", pos):
            depth -= 1
            result[pos:pos + 2] = "  "
            pos += 2
        elif depth or source.startswith("--", pos):
            if not depth:
                end = source.find("\n", pos)
                end = len(source) if end < 0 else end
                result[pos:end] = " " * (end - pos)
                pos = end
            else:
                if source[pos] != "\n":
                    result[pos] = " "
                pos += 1
        else:
            pos += 1
    if depth:
        raise RuntimeError("unclosed Lean comment")
    return "".join(result)


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
    roots = external_roots()
    for module, entry in zip(modules, entries, strict=True):
        if entry.get("errors") or not isinstance(entry.get("result"), dict):
            raise RuntimeError(f"{module}: Lean rejected the import header: {entry.get('errors')}")
        declarations = entry["result"].get("imports")
        if not isinstance(declarations, list):
            raise RuntimeError(f"{module}: Lean returned no imports")
        imports = {row["module"] for row in declarations}
        local = imports & modules.keys()
        for dep in sorted(imports - local):
            if not resolved_external(dep, roots):
                failures.append(f"{module}: import outside five libraries and pinned packages: {dep}")
        graph[module] = local
        if module == "FastConfirmation":
            continue
        source = owner(module)
        if source is None:
            failures.append(f"{module}: outside the five libraries")
        for dep in sorted(imports):
            target = owner(dep)
            if target is not None and source in SPEC and target in SPEC and SPEC.index(target) > SPEC.index(source):
                failures.append(f"{module}: reverse library import {dep}")
    if graph["FastConfirmation"] != set(LIBRARIES):
        failures.append("root aggregate must import exactly the five library roots")
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
    }
    found: set[tuple[str, str]] = set()
    for module, path in modules.items():
        if owner(module) not in SPEC[:2]:
            continue
        for match in theorem_pattern.finditer(without_comments(path.read_text())):
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
    print(f"import architecture audit passed: {count} modules, five libraries")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
