#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mode="full"
if [[ -n "${CONSENSUS_SPECS_REPO:-}" ]]; then
  consensus_repo="$CONSENSUS_SPECS_REPO"
elif [[ -d "$repo_root/../consensus-specs" ]]; then
  consensus_repo="$repo_root/../consensus-specs"
else
  consensus_repo="$repo_root/../../consensus-specs"
fi

while (($#)); do
  case "$1" in
    --fast)
      mode="fast"
      shift
      ;;
    --consensus-repo)
      if (($# < 2)); then
        echo "--consensus-repo requires a path" >&2
        exit 2
      fi
      consensus_repo="$2"
      shift 2
      ;;
    -h|--help)
      echo "usage: scripts/validate.sh [--fast] [--consensus-repo PATH]"
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      exit 2
      ;;
  esac
done

cd "$repo_root"

python3 scripts/check_consensus_source.py --repo "$consensus_repo"
set +e
forbidden_findings="$(
  git grep --untracked --exclude-standard -nF \
    -e 'sorry' -e '#exit' -e 'native_decide' -e 'bv_decide' \
    -e 'implemented_by' -e 'native :=' -e 'native:=' \
    -e '+native' -e '+ native' -- \
    FastConfirmation.lean FastConfirmation lakefile.toml
)"
forbidden_status=$?
set -e
if ((forbidden_status == 0)); then
  echo "project source/configuration contains a forbidden exact string:" >&2
  echo "$forbidden_findings" >&2
  exit 1
elif ((forbidden_status != 1)); then
  echo "exact-string scan failed with status $forbidden_status" >&2
  exit "$forbidden_status"
fi
git diff --check
git diff --cached --check
set +e
whitespace_findings="$(
  git grep --untracked --exclude-standard -nI -E '[[:blank:]]+$' -- \
    .github AGENTS.md FastConfirmation FastConfirmation.lean LICENSE README.md \
    docs lake-manifest.json lakefile.toml lean-toolchain scripts spec_source
)"
whitespace_status=$?
set -e
if ((whitespace_status == 0)); then
  echo "tracked/untracked project text contains trailing whitespace:" >&2
  echo "$whitespace_findings" >&2
  exit 1
elif ((whitespace_status != 1)); then
  echo "trailing-whitespace scan failed with status $whitespace_status" >&2
  exit "$whitespace_status"
fi

if [[ "$mode" == "full" ]]; then
  python3 scripts/check_imports.py
  scripts/check_build.sh
  lake env lean scripts/Audit.lean
  git diff --exit-code -- lake-manifest.json
fi

echo "validation passed ($mode)"
