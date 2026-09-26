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
EXPECTED_TOP_LEVEL_KEYS = {"schema", "repository", "commit", "fork_commit", "license", "files"}
EXPECTED_FILE_KEYS = {"path", "role", "git_blob", "bytes", "sha256"}
EXPECTED_REPOSITORY = "https://github.com/ethereum/consensus-specs.git"
EXPECTED_COMMIT = "6b9bd532cca16555e2f3282d757622ebff29743e"
EXPECTED_FORK_COMMIT = "13f391516352f61b3ac5dcaae5be1884d104f86a"
EXPECTED_GLOAS_DISCOUNT_SHA256 = "e62ba45c9024b6621493b9b2ac7a21913bd6426a61b3e02827e164ac4968742b"
EXPECTED_LICENSE = "CC0-1.0"
EXPECTED_ROLES = {
    "specs/gloas/validator.md": "Gloas honest validator behavior",
    "specs/gloas/fork-choice.md": "Gloas fork-choice environment",
    "specs/gloas/fast-confirmation.md": "Gloas Fast Confirmation Rule overlay",
    "specs/gloas/beacon-chain.md": "Gloas beacon-chain types and helpers",
    "presets/mainnet/gloas.yaml": "Mainnet Gloas preset values consumed by Config",
    "presets/minimal/gloas.yaml": "Minimal Gloas preset values consumed by conformance",
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
    if value["fork_commit"] != EXPECTED_FORK_COMMIT:
        raise ManifestError("manifest must pin the fork commit")
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
        extra = {"fork_git_blob", "fork_bytes", "fork_sha256"} if entry.get("path") == "specs/gloas/fast-confirmation.md" else set()
        require_exact_keys(entry, EXPECTED_FILE_KEYS | extra, f"files[{index}]")
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
    head = str(run_git(repo, ["rev-parse", "--verify", "HEAD^{commit}"])).strip()
    if head != EXPECTED_FORK_COMMIT:
        raise ManifestError(
            f"checkout HEAD differs from pinned fork commit: "
            f"{head} != {EXPECTED_FORK_COMMIT}"
        )
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

        # The manifest pins upstream objects. The working files must also
        # match the fork commit, which changes the Gloas discount overlay.
        fork_line = str(
            run_git(repo, ["ls-tree", EXPECTED_FORK_COMMIT, "--", source_path])
        ).strip()
        fork_fields = fork_line.split(maxsplit=3)
        if len(fork_fields) != 4:
            raise ManifestError(f"missing or malformed fork tree entry for {source_path}")
        fork_mode, fork_kind, fork_blob, fork_path = fork_fields
        if fork_mode != "100644" or fork_kind != "blob" or fork_path != source_path:
            raise ManifestError(
                f"fork tree identity mismatch for {source_path}: {fork_line!r}"
            )
        fork_content = run_git(repo, ["cat-file", "blob", fork_blob], binary=True)
        assert isinstance(fork_content, bytes)
        try:
            local_content = (repo / source_path).read_bytes()
        except OSError as exc:
            raise ManifestError(f"cannot read working file {source_path}: {exc}") from exc
        if local_content != fork_content:
            raise ManifestError(f"working file differs from pinned fork: {source_path}")
        if source_path == "specs/gloas/fast-confirmation.md":
            if (fork_blob != entry["fork_git_blob"] or
                    len(fork_content) != entry["fork_bytes"]):
                raise ManifestError("fork Gloas overlay identity differs from manifest")
            fork_hash = hashlib.sha256(fork_content).hexdigest()
            if fork_hash != entry["fork_sha256"]:
                raise ManifestError("fork Gloas overlay hash differs from manifest")
            if fork_hash != EXPECTED_GLOAS_DISCOUNT_SHA256:
                raise ManifestError(
                    "Gloas discount overlay differs from documented deviation: "
                    f"{fork_hash} != {EXPECTED_GLOAS_DISCOUNT_SHA256}"
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
        f"consensus source audit passed: {len(entries)} working files at {EXPECTED_FORK_COMMIT} "
        f"with upstream objects at {EXPECTED_COMMIT}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
