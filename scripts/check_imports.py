#!/usr/bin/env python3
"""Check the five-library import order and the provenance of every import.

Lean's parser gives the imports of each project file. Each import is then
resolved on the Lake search path (`lake env`) with Lean's rule: the first
search path entry that holds the root name of the module supplies it. An
external import must resolve to exactly one entry, in the toolchain or in a
package that `lake-manifest.json` pins, and its source file must be tracked
at the pinned revision. A project import must not resolve outside the project
build folder. Local Lean files outside the libraries are rejected, so a local
file cannot shadow a package module name.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = tuple("FastConfirmation" + name for name in
             ("Model", "Statements", "Internal", "Proofs", "Witnesses"))
LIBRARIES = SPEC
AGGREGATE = "FastConfirmation"
# Folders that hold Lean scripts, not library modules. They are not on a
# search path and no lean_lib glob names them.
SCRIPT_FOLDERS = ("scripts",)


def owner(module: str) -> str | None:
    return next((lib for lib in LIBRARIES
                 if module == lib or module.startswith(lib + ".")), None)


def is_project(module: str) -> bool:
    return module == AGGREGATE or owner(module) is not None


def closure(start: str, graph: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    pending = [start]
    while pending:
        current = pending.pop()
        if current not in seen:
            seen.add(current)
            pending.extend(graph.get(current, set()) - seen)
    return seen


def git(folder: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(folder), *args], text=True)


def real(path: Path) -> Path:
    return Path(os.path.realpath(path))


class Resolver:
    """Resolve module names as `lake env lean` does, and prove their origin."""

    def __init__(self, root: Path = ROOT) -> None:
        self.root = root
        env = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=root,
                             capture_output=True, text=True, timeout=120)
        if env.returncode:
            raise RuntimeError(f"lake env failed: {env.stderr.strip()}")
        prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
        # Lean appends its built-in library folder to LEAN_PATH.
        entries = [Path(part) for part in env.stdout.strip().split(":") if part]
        entries.append(prefix / "lib" / "lean")
        self.entries: list[Path] = []
        for entry in map(real, entries):
            if entry not in self.entries:
                self.entries.append(entry)
        self.project_build = real(root / ".lake" / "build" / "lib" / "lean")
        self.toolchain_lib = real(prefix / "lib" / "lean")
        self.toolchain_sources = (prefix / "src" / "lean", prefix / "src" / "lean" / "lake")
        self.packages: dict[Path, tuple[str, set[str]]] = {}
        manifest = json.loads((root / "lake-manifest.json").read_text())
        for package in manifest["packages"]:
            name, rev = package["name"], package.get("rev")
            folder = root / ".lake" / "packages" / name
            if not rev or not folder.is_dir():
                raise RuntimeError(f"missing pinned package: {name}")
            if git(folder, "rev-parse", "HEAD").strip() != rev:
                raise RuntimeError(f"package {name} differs from lake-manifest.json")
            if git(folder, "status", "--porcelain", "--untracked-files=no").strip():
                raise RuntimeError(f"pinned package {name} has changed source files")
            tracked = set(filter(None, git(folder, "ls-files", "-z").split("\0")))
            self.packages[real(folder / ".lake" / "build" / "lib" / "lean")] = (name, tracked)

    def holders(self, module: str) -> list[Path]:
        head = module.split(".", 1)[0]
        return [entry for entry in self.entries
                if (entry / head).is_dir() or (entry / f"{head}.olean").exists()]

    def origin(self, module: str) -> str:
        """Return `project`, `toolchain` or `package:<name>`, or raise."""
        relative = Path(*module.split("."))
        holders = self.holders(module)
        if len(holders) > 1:
            raise RuntimeError(f"{module}: root name in more than one search path entry: "
                               f"{[str(entry) for entry in holders]}")
        if is_project(module):
            if holders and holders[0] != self.project_build:
                raise RuntimeError(f"{module}: project module resolves outside the project "
                                   f"build folder: {holders[0]}")
            if not (self.root / relative.with_suffix(".lean")).is_file():
                raise RuntimeError(f"{module}: project module has no source file")
            return "project"
        if not holders:
            raise RuntimeError(f"{module}: no search path entry holds it")
        entry = holders[0]
        olean = entry / relative.with_suffix(".olean")
        if not olean.is_file() or not real(olean).is_relative_to(entry):
            raise RuntimeError(f"{module}: resolved object file is absent or links outside "
                               f"its entry: {olean}")
        source = relative.with_suffix(".lean")
        if entry == self.toolchain_lib:
            if not any((folder / source).is_file() for folder in self.toolchain_sources):
                raise RuntimeError(f"{module}: toolchain object file has no toolchain source")
            return "toolchain"
        if entry in self.packages:
            name, tracked = self.packages[entry]
            if source.as_posix() not in tracked:
                raise RuntimeError(f"{module}: source {source} is not tracked by pinned "
                                   f"package {name}")
            return f"package:{name}"
        raise RuntimeError(f"{module}: resolves outside the project, toolchain, and pinned "
                           f"packages: {entry}")


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


def code_tokens(source: str) -> str:
    """Blank comments, string literals and quoted identifiers `«...»`."""
    text = without_comments(source)
    return re.sub(r'"(?:[^"\\\n]|\\.)*"|«[^»]*»',
                  lambda match: re.sub(r"[^\n]", " ", match.group()), text)


def local_lean_files() -> list[str]:
    """Return Lean files outside the libraries, the aggregate and scripts."""
    allowed = {f"{name}.lean" for name in (AGGREGATE, *LIBRARIES)}
    found = []
    for folder, children, files in os.walk(ROOT):
        relative = Path(folder).relative_to(ROOT)
        top = relative.parts[0] if relative.parts else ""
        if top in (".git", ".lake", *LIBRARIES, *SCRIPT_FOLDERS):
            children[:] = []
            continue
        found += [str(relative / name) for name in files
                  if name.endswith(".lean") and str(relative / name) not in allowed]
    return sorted(found)


def check_lakefile() -> list[str]:
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    libraries = {lib["name"]: lib for lib in config.get("lean_lib", [])}
    expected = {name: [name, f"{name}.+"] for name in LIBRARIES}
    expected[AGGREGATE] = [AGGREGATE]
    failures = []
    if set(libraries) != set(expected):
        failures.append(f"lakefile libraries differ: {sorted(libraries)}")
    for name, globs in expected.items():
        lib = libraries.get(name, {})
        if lib.get("globs") != globs or set(lib) - {"name", "globs", "leanOptions"}:
            failures.append(f"lakefile library {name} has changed module sources")
    if config.get("lean_exe") or config.get("input_file") or config.get("input_dir"):
        failures.append("lakefile declares extra build targets")
    return failures


def audit() -> tuple[int, int, list[str]]:
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
    failures = check_lakefile()
    failures += [f"{path}: Lean file outside the five libraries" for path in local_lean_files()]
    graph: dict[str, set[str]] = {}
    resolver = Resolver()
    origins: dict[str, str] = {}
    for module, entry in zip(modules, entries, strict=True):
        if entry.get("errors") or not isinstance(entry.get("result"), dict):
            raise RuntimeError(f"{module}: Lean rejected the import header: {entry.get('errors')}")
        declarations = entry["result"].get("imports")
        if not isinstance(declarations, list):
            raise RuntimeError(f"{module}: Lean returned no imports")
        imports = {row["module"] for row in declarations}
        for dep in sorted(imports):
            if dep not in origins:
                try:
                    origins[dep] = resolver.origin(dep)
                except RuntimeError as exc:
                    origins[dep] = "rejected"
                    failures.append(f"{module}: import provenance: {exc}")
            if origins[dep] == "project" and dep not in modules:
                failures.append(f"{module}: import of an unknown project module: {dep}")
        graph[module] = imports & modules.keys()
        if module == AGGREGATE:
            continue
        source = owner(module)
        if source is None:
            failures.append(f"{module}: outside the five libraries")
        for dep in sorted(imports):
            target = owner(dep)
            if target is not None and source in SPEC and target in SPEC and SPEC.index(target) > SPEC.index(source):
                failures.append(f"{module}: reverse library import {dep}")
    if graph[AGGREGATE] != set(LIBRARIES):
        failures.append("root aggregate must import exactly the five library roots")
    for lib in LIBRARIES:
        owned = {module for module in modules if owner(module) == lib}
        orphaned = owned - closure(lib, graph)
        if orphaned:
            failures.append(f"{lib}: orphan modules {sorted(orphaned)}")
    orphaned = modules.keys() - closure(AGGREGATE, graph)
    if orphaned:
        failures.append(f"root aggregate orphan modules {sorted(orphaned)}")
    # Defense in depth for scripts/Audit.lean, which rejects authored proofs in
    # the environment: an `example` leaves no declaration, so the scan also
    # rejects the proof keywords in the code of Model and Statements.
    keyword = re.compile(r"(?<![\w.'?!])(theorem|lemma|example)(?![\w'?!])")
    allowed = {("FastConfirmationModel.Execution.ScheduledPrefixes", "theorem"): 1}
    found: dict[tuple[str, str], int] = {}
    for module, path in modules.items():
        if owner(module) not in SPEC[:2]:
            continue
        for match in keyword.finditer(code_tokens(path.read_text())):
            key = (module, match.group(1))
            found[key] = found.get(key, 0) + 1
    for key, count in sorted(found.items()):
        if count > allowed.get(key, 0):
            failures.append(f"{key[0]}: `{key[1]}` keyword in Model or Statements")
    if any(found.get(key, 0) != count for key, count in allowed.items()):
        failures.append(f"missing required proof terms: {sorted(allowed)}")
    external = sum(origin != "project" for origin in origins.values())
    return len(modules), external, failures


def main() -> int:
    try:
        count, external, failures = audit()
        if failures:
            raise RuntimeError("\n".join(failures))
    except (RuntimeError, OSError, ValueError, KeyError, subprocess.SubprocessError,
            tomllib.TOMLDecodeError) as exc:
        print(f"import architecture audit failed:\n{exc}", file=sys.stderr)
        return 1
    print(f"import architecture audit passed: {count} modules, five libraries, "
          f"{external} resolved external imports")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
