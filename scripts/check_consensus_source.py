#!/usr/bin/env python3
"""Verify the exact consensus-spec Git objects claimed by the public model."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "spec_source" / "manifest.json"
EXPECTED_TOP_LEVEL_KEYS = {"schema", "repository", "commit", "license", "files"}
EXPECTED_FILE_KEYS = {"path", "role", "git_blob", "bytes", "sha256"}
EXPECTED_REPOSITORY = "https://github.com/ethereum/consensus-specs.git"
EXPECTED_COMMIT = "477321355d48d527e7e1e4d572f6a40a0b41072a"
EXPECTED_LICENSE = "CC0-1.0"
EXPECTED_ROLES = {
    "specs/phase0/fast-confirmation.md":
        "Fast Confirmation Rule executable specification",
    "specs/phase0/fork-choice.md": "Phase 0 fork-choice environment",
    "specs/phase0/beacon-chain.md": "Phase 0 beacon-chain helpers and state",
    "specs/phase0/validator.md": "Phase 0 honest validator behavior",
    "presets/mainnet/phase0.yaml":
        "Mainnet Phase 0 preset values consumed by Config",
    "configs/mainnet.yaml": "Mainnet configuration values consumed by Config",
}
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")


class ManifestError(RuntimeError):
    pass


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ManifestError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_manifest() -> dict[str, Any]:
    try:
        raw = MANIFEST_PATH.read_text(encoding="utf-8")
        value = json.loads(raw, object_pairs_hook=reject_duplicate_keys)
    except (OSError, json.JSONDecodeError, ManifestError) as exc:
        raise ManifestError(f"cannot load {MANIFEST_PATH}: {exc}") from exc
    if not isinstance(value, dict):
        raise ManifestError("manifest root must be an object")
    return value


def require_exact_keys(value: dict[str, Any], expected: set[str], label: str) -> None:
    actual = set(value)
    if actual != expected:
        missing = sorted(expected - actual)
        unknown = sorted(actual - expected)
        raise ManifestError(
            f"{label} keys differ; missing={missing}, unknown={unknown}"
        )


def validate_manifest(value: dict[str, Any]) -> list[dict[str, Any]]:
    require_exact_keys(value, EXPECTED_TOP_LEVEL_KEYS, "manifest")
    if type(value["schema"]) is not int or value["schema"] != 1:
        raise ManifestError("manifest schema must be exactly 1")
    if value["repository"] != EXPECTED_REPOSITORY:
        raise ManifestError("unexpected consensus-specs repository URL")
    if value["commit"] != EXPECTED_COMMIT or not HEX40.fullmatch(value["commit"]):
        raise ManifestError("manifest must use the canonical public 40-hex commit")
    if value["license"] != EXPECTED_LICENSE:
        raise ManifestError("unexpected source SPDX license")

    files = value["files"]
    if not isinstance(files, list) or not files:
        raise ManifestError("files must be a nonempty array")

    checked: list[dict[str, Any]] = []
    seen: set[str] = set()
    for index, entry in enumerate(files):
        if not isinstance(entry, dict):
            raise ManifestError(f"files[{index}] must be an object")
        require_exact_keys(entry, EXPECTED_FILE_KEYS, f"files[{index}]")
        source_path = entry["path"]
        if not isinstance(source_path, str) or source_path not in EXPECTED_ROLES:
            raise ManifestError(f"unexpected source path: {source_path!r}")
        if source_path in seen:
            raise ManifestError(f"duplicate source path: {source_path}")
        seen.add(source_path)
        if entry["role"] != EXPECTED_ROLES[source_path]:
            raise ManifestError(f"unexpected role for {source_path}")
        if not isinstance(entry["git_blob"], str) or not HEX40.fullmatch(
            entry["git_blob"]
        ):
            raise ManifestError(f"invalid Git blob ID for {source_path}")
        if (
            not isinstance(entry["sha256"], str)
            or not HEX64.fullmatch(entry["sha256"])
        ):
            raise ManifestError(f"invalid SHA-256 for {source_path}")
        if (
            isinstance(entry["bytes"], bool)
            or not isinstance(entry["bytes"], int)
            or entry["bytes"] <= 0
        ):
            raise ManifestError(f"invalid byte length for {source_path}")
        checked.append(entry)

    expected_paths = set(EXPECTED_ROLES)
    if seen != expected_paths:
        raise ManifestError(
            f"source allowlist differs; missing={sorted(expected_paths - seen)}"
        )
    return checked


def run_git(repo: Path, args: list[str], *, binary: bool = False) -> str | bytes:
    try:
        completed = subprocess.run(
            ["git", "--no-replace-objects", "-C", str(repo), *args],
            check=True,
            capture_output=True,
            timeout=30,
            text=not binary,
        )
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        raise ManifestError(f"git {' '.join(args)} failed: {exc}") from exc
    return completed.stdout


def verify_objects(repo: Path, entries: list[dict[str, Any]]) -> None:
    if not repo.is_dir():
        raise ManifestError(f"consensus-specs checkout is not a directory: {repo}")
    object_type = str(run_git(repo, ["cat-file", "-t", EXPECTED_COMMIT])).strip()
    if object_type != "commit":
        raise ManifestError(f"{EXPECTED_COMMIT} is not a commit object")

    for entry in entries:
        source_path = entry["path"]
        tree_line = str(
            run_git(repo, ["ls-tree", EXPECTED_COMMIT, "--", source_path])
        ).strip()
        fields = tree_line.split(maxsplit=3)
        if len(fields) != 4:
            raise ManifestError(f"missing or malformed tree entry for {source_path}")
        mode, kind, blob, returned_path = fields
        if (
            mode != "100644"
            or kind != "blob"
            or returned_path != source_path
            or blob != entry["git_blob"]
        ):
            raise ManifestError(
                f"tree identity mismatch for {source_path}: {tree_line!r}"
            )

        content = run_git(repo, ["cat-file", "blob", blob], binary=True)
        assert isinstance(content, bytes)
        actual_sha256 = hashlib.sha256(content).hexdigest()
        if len(content) != entry["bytes"]:
            raise ManifestError(
                f"byte length mismatch for {source_path}: "
                f"{len(content)} != {entry['bytes']}"
            )
        if actual_sha256 != entry["sha256"]:
            raise ManifestError(
                f"SHA-256 mismatch for {source_path}: "
                f"{actual_sha256} != {entry['sha256']}"
            )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repo",
        type=Path,
        required=True,
        help="consensus-specs Git checkout containing the pinned commit object",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        entries = validate_manifest(load_manifest())
        verify_objects(args.repo.resolve(), entries)
    except ManifestError as exc:
        print(f"consensus source audit failed: {exc}", file=sys.stderr)
        return 1
    print(
        f"consensus source audit passed: {len(entries)} files at {EXPECTED_COMMIT}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
