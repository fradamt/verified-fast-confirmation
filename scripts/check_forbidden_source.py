#!/usr/bin/env python3
"""Reject declarations and metaprogramming that can evade kernel trust checks."""
from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIBS = ("FastConfirmationModel", "FastConfirmationStatements",
        "FastConfirmationInternal", "FastConfirmationProofs",
        "FastConfirmationWitnesses")
PATTERN = re.compile(
    r"\b(?:sorry|admit|native_decide|bv_decide|implemented_by|extern|unsafe|"
    r"run_cmd|run_meta|run_elab|elab|elab_rules|initialize|macro|macro_rules|syntax|"
    r"addDecl|addDeclCore|addDeclWithoutChecking|modifyEnv|setEnv|ofReduceBool|"
    r"trustCompiler)\b|#eval\b|"
    r"debug\.skipKernelTC|Environment\.addDeclCore|\bmeta\s+import\b|"
    r"\b(?:native\s*:=|\+\s*native)"
)


def code_only(source: str) -> str:
    out = list(source)
    i = 0
    depth = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            out[i:i + 2] = "  "
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            out[i:i + 2] = "  "
            i += 2
        elif depth or source.startswith("--", i):
            if not depth:
                end = source.find("\n", i)
                end = len(source) if end < 0 else end
                out[i:end] = " " * (end - i)
                i = end
            else:
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        else:
            i += 1
    if depth:
        raise ValueError("unclosed Lean comment")
    return "".join(out)


def check() -> list[str]:
    paths = [ROOT / "FastConfirmation.lean", *(ROOT / f"{lib}.lean" for lib in LIBS)]
    paths += [path for lib in LIBS for path in (ROOT / lib).rglob("*.lean")]
    findings = []
    for path in paths:
        source = code_only(path.read_text())
        for match in PATTERN.finditer(source):
            # This one tactic macro expands to dsimp and omega. It has no
            # command elaborator and cannot edit the environment.
            if (match.group() == "macro" and
                    path.relative_to(ROOT).as_posix() ==
                    "FastConfirmationProofs/FFG/Concrete/TransitionFrames.lean" and
                    source[match.start():].startswith('macro "beacon_omega" : tactic =>')):
                continue
            line = source.count("\n", 0, match.start()) + 1
            findings.append(f"{path.relative_to(ROOT)}:{line}: {match.group()}")
    return findings


if __name__ == "__main__":
    failures = check()
    if failures:
        raise SystemExit("forbidden project source:\n" + "\n".join(failures))
    print("forbidden project source check passed")
