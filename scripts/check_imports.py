#!/usr/bin/env python3
"""Check facade reachability using the pinned Lean parser's import graph."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "FastConfirmation.lean"
LEAN_TREE = ROOT / "FastConfirmation"


class ImportAuditError(RuntimeError):
    pass


def project_lean_paths() -> list[Path]:
    if LEAN_ROOT.is_symlink() or LEAN_TREE.is_symlink():
        raise ImportAuditError("refusing symlinked project root")
    if not LEAN_ROOT.is_file() or not LEAN_TREE.is_dir():
        raise ImportAuditError("project Lean roots are missing or have the wrong type")
    for entry in LEAN_TREE.rglob("*"):
        if entry.is_symlink():
            raise ImportAuditError(f"refusing symlink in project source tree: {entry}")
    return [LEAN_ROOT, *sorted(LEAN_TREE.rglob("*.lean"))]


def module_for(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def lean_imports(paths: list[Path]) -> list[set[str]]:
    relative_paths = [str(path.relative_to(ROOT)) for path in paths]
    try:
        result = subprocess.run(
            ["lean", "--deps-json", *relative_paths],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ImportAuditError(f"could not run pinned Lean import parser: {exc}") from exc
    if result.returncode != 0:
        raise ImportAuditError(
            "Lean import parser failed"
            + (f":\n{result.stderr.strip()}" if result.stderr.strip() else "")
        )
    try:
        payload = json.loads(result.stdout)
        parsed = payload["imports"]
    except (json.JSONDecodeError, KeyError, TypeError) as exc:
        raise ImportAuditError("Lean import parser returned malformed JSON") from exc
    if len(parsed) != len(paths):
        raise ImportAuditError(
            f"Lean parsed {len(parsed)} headers for {len(paths)} source files"
        )

    imports: list[set[str]] = []
    for path, entry in zip(paths, parsed, strict=True):
        errors = entry.get("errors")
        result_payload = entry.get("result")
        if errors or not isinstance(result_payload, dict):
            raise ImportAuditError(
                f"{path.relative_to(ROOT)}: Lean rejected the module header: {errors!r}"
            )
        declarations = result_payload.get("imports")
        if not isinstance(declarations, list):
            raise ImportAuditError(
                f"{path.relative_to(ROOT)}: Lean returned no import list"
            )
        names: set[str] = set()
        for declaration in declarations:
            name = declaration.get("module") if isinstance(declaration, dict) else None
            if not isinstance(name, str):
                raise ImportAuditError(
                    f"{path.relative_to(ROOT)}: malformed Lean import entry"
                )
            names.add(name)
        imports.append(names)
    return imports


def reachable(start: str, graph: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    pending = [start]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        pending.extend(sorted(graph.get(module, set()) - seen))
    return seen


def main() -> int:
    try:
        paths = project_lean_paths()
        modules = {module_for(path): path for path in paths}
        if len(modules) != len(paths):
            raise ImportAuditError("duplicate module path")

        parsed_imports = lean_imports(paths)
        graph: dict[str, set[str]] = {}
        failures: list[str] = []
        for (module, _), imports in zip(modules.items(), parsed_imports, strict=True):
            local_imports = {
                name for name in imports if name.startswith("FastConfirmation")
            }
            missing = sorted(local_imports - modules.keys())
            if missing:
                failures.append(f"{module}: missing local imports {missing}")
            graph[module] = local_imports & modules.keys()

        expected_roots = {
            "FastConfirmation",
            "FastConfirmation.Spec",
            "FastConfirmation.Paper",
        }
        if not expected_roots <= modules.keys():
            raise ImportAuditError(
                f"missing facade modules: {sorted(expected_roots - modules.keys())}"
            )
        spec_modules = {
            name
            for name in modules
            if name == "FastConfirmation.Spec"
            or name.startswith("FastConfirmation.Spec.")
        }
        paper_modules = {
            name
            for name in modules
            if name == "FastConfirmation.Paper"
            or name.startswith("FastConfirmation.Paper.")
        }
        unclassified = sorted(
            modules.keys() - spec_modules - paper_modules - {"FastConfirmation"}
        )
        if unclassified:
            failures.append(f"modules outside Spec/Paper architecture: {unclassified}")

        spec_reachable = reachable("FastConfirmation.Spec", graph)
        paper_reachable = reachable("FastConfirmation.Paper", graph)
        root_reachable = reachable("FastConfirmation", graph)
        spec_unreachable = sorted(spec_modules - spec_reachable)
        paper_unreachable = sorted(paper_modules - paper_reachable)
        root_unreachable = sorted(modules.keys() - root_reachable)
        if spec_unreachable:
            failures.append(f"Spec facade orphan modules: {spec_unreachable}")
        if paper_unreachable:
            failures.append(f"Paper facade orphan modules: {paper_unreachable}")
        if root_unreachable:
            failures.append(f"repository facade orphan modules: {root_unreachable}")

        spec_cross = sorted(spec_reachable & paper_modules)
        paper_cross = sorted(paper_reachable & spec_modules)
        if spec_cross:
            failures.append(
                f"Spec facade transitively imports Paper modules: {spec_cross}"
            )
        if paper_cross:
            failures.append(
                f"Paper facade transitively imports Spec modules: {paper_cross}"
            )
        if graph["FastConfirmation"] != {
            "FastConfirmation.Spec",
            "FastConfirmation.Paper",
        }:
            failures.append(
                "FastConfirmation.lean must directly compose exactly the Spec "
                "and Paper facades"
            )
        if failures:
            raise ImportAuditError("\n".join(failures))
    except ImportAuditError as exc:
        print(f"import architecture audit failed:\n{exc}", file=sys.stderr)
        return 1

    print(
        "import architecture audit passed: "
        f"{len(spec_modules)} Spec, {len(paper_modules)} Paper, "
        f"{len(modules)} total modules"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
