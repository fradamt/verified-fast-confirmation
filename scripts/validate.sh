#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mode="full"
if [[ -n "${CONSENSUS_SPECS_REPO:-}" ]]; then
  consensus_repo="$CONSENSUS_SPECS_REPO"
else
  # Default: nearest `consensus-specs` sibling at or above the repository root.
  consensus_repo="$repo_root/../consensus-specs"
  probe="$repo_root"
  while [[ "$probe" != "/" ]]; do
    probe="$(dirname "$probe")"
    if [[ -d "$probe/consensus-specs" ]]; then
      consensus_repo="$probe/consensus-specs"
      break
    fi
  done
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
    FastConfirmation.lean FastConfirmationModel.lean FastConfirmationModel FastConfirmationStatements.lean FastConfirmationStatements FastConfirmationInternal.lean FastConfirmationInternal FastConfirmationProofs.lean FastConfirmationProofs FastConfirmationWitnesses.lean FastConfirmationWitnesses FastConfirmationPaper.lean FastConfirmationPaper lakefile.toml
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
    .github FastConfirmation.lean FastConfirmationModel.lean FastConfirmationModel FastConfirmationStatements.lean FastConfirmationStatements FastConfirmationInternal.lean FastConfirmationInternal FastConfirmationProofs.lean FastConfirmationProofs FastConfirmationWitnesses.lean FastConfirmationWitnesses FastConfirmationPaper.lean FastConfirmationPaper LICENSE README.md \
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

python3 scripts/check_synchrony_corners.py --self-test
python3 scripts/check_doc_names.py
python3 scripts/check_review_boundary.py
python3 scripts/check_review_boundary.py --self-test
if [[ -x "$consensus_repo/.venv/bin/python" ]]; then
  python3 scripts/conformance/contracts/check_inventory.py --repo "$consensus_repo"
elif [[ "${REQUIRE_PYSPEC:-0}" == "1" ]]; then
  echo "pyspec interpreter is required at $consensus_repo/.venv/bin/python" >&2
  exit 1
else
  echo "SKIPPED: pyspec contract and projection checks; interpreter absent at $consensus_repo/.venv/bin/python"
  python3 scripts/conformance/contracts/check_inventory.py --inventory-only
fi
python3 scripts/conformance/concrete/check_source_inventory.py --repo "$consensus_repo"
if [[ -x "$consensus_repo/.venv/bin/python" ]]; then
  "$consensus_repo/.venv/bin/python" scripts/conformance/contracts/test_realized_gap.py --repo "$consensus_repo"
  # The differential runner imports the concrete transition module.
  lake build FastConfirmationModel.Spec.BeaconChain.ConcreteTransition
  PYTHONDONTWRITEBYTECODE=1 "$consensus_repo/.venv/bin/python" \
    scripts/conformance/concrete/run_differential.py --consensus-repo "$consensus_repo"
else
  echo "realized-gap regression and concrete differential skipped: pinned pyspec interpreter is absent"
fi

if [[ "$mode" == "full" ]]; then
  scripts/check_build.sh
  python3 scripts/check_imports.py
  reachability_output="$(mktemp)"
  lake env lean scripts/StatementReachability.lean > "$reachability_output"
  cat "$reachability_output"
  python3 scripts/conformance/contracts/check_inventory.py --inventory-only --reachable-file "$reachability_output"
  rm "$reachability_output"
  lake env lean scripts/ReviewSurfaceShape.lean
  lake env lean scripts/Audit.lean
  git diff --exit-code -- lake-manifest.json
fi

echo "validation passed ($mode)"
