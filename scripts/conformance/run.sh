#!/usr/bin/env bash
set -euo pipefail

if [[ $# -eq 2 ]]; then
  consensus_specs_dir=$1
  fork=gloas
  preset=minimal
  out=$2
elif [[ $# -eq 4 ]]; then
  consensus_specs_dir=$1
  fork=$2
  preset=$3
  out=$4
else
  echo "usage: scripts/conformance/run.sh <consensus-specs-dir> [gloas minimal] <out.jsonl>" >&2
  exit 2
fi

if [[ "$fork" != gloas ]]; then
  echo "schema v2 requires Gloas; pre-Gloas traces describe historical phase0 stores" >&2
  exit 2
fi
if [[ ! -x "$consensus_specs_dir/.venv/bin/python" ]]; then
  echo "MISSING_PYSPEC: $consensus_specs_dir/.venv/bin/python; no setup or network attempted" >&2
  exit 2
fi
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
plugin_dir="$repo_root/scripts/conformance/python"
mkdir -p "$(dirname "$out")"
out="$(cd "$(dirname "$out")" && pwd)/$(basename "$out")"
tmp_dir="$(mktemp -d "$repo_root/.conformance.XXXXXX")"
trace_base="$tmp_dir/trace.jsonl"
pytest_log="$out.pytest.log"
runner_log="$out.runner.log"
trap 'rm -rf "$tmp_dir"' EXIT

export_start=$SECONDS
pytest_parallel=${MAYBE_PARALLEL:-}
export FCR_TRACE_OUT="$trace_base"
export UV_OFFLINE=1
export UV_NO_SYNC=1
export PYTHONDONTWRITEBYTECODE=1
set +e
(
  cd "$consensus_specs_dir" || exit 1
  PYTHONPATH="$plugin_dir${PYTHONPATH:+:$PYTHONPATH}" \
    .venv/bin/python -m pytest "tests/core/pyspec/eth_consensus_specs/test/phase0/fast_confirmation" \
      ${pytest_parallel} --reftests --fork="$fork" --preset="$preset" -p fcr_trace_plugin -p no:cacheprovider
) >"$pytest_log" 2>&1
pytest_status=$?
set -e

shopt -s nullglob
trace_files=("$tmp_dir"/trace*.jsonl)
: >"$out"
if [[ ${#trace_files[@]} -gt 0 ]]; then
  cat "${trace_files[@]}" >>"$out"
fi
record_count=$(wc -l <"$out" | tr -d ' ')
echo "records=$record_count"
echo "export-wall-seconds=$((SECONDS - export_start))"
if [[ $pytest_status -ne 0 ]]; then
  echo "pytest-status=$pytest_status log=$pytest_log"
  rg -n -m 20 "FAILED|ERROR|E   " "$pytest_log" || true
fi
if [[ $record_count -eq 0 ]]; then
  echo "MISSING_TRACE: no Gloas FCR records were exported" >&2
  exit 1
fi
python3 "$plugin_dir/check_trace.py" "$out"
if [[ "${FCR_EXPORT_ONLY:-${FCR_SKIP_LEAN:-0}}" == 1 ]]; then
  echo "export-only: records=$record_count trace=$out pytest-status=$pytest_status"
  exit "$pytest_status"
fi

runner_start=$SECONDS
set +e
# Optional lock for machines that share one Lean build slot: FCR_LEAN_LOCK=<lock file>.
lock=()
if [[ -n "${FCR_LEAN_LOCK:-}" ]]; then lock=(flock "$FCR_LEAN_LOCK"); fi
(cd "$repo_root" && ${lock[@]+"${lock[@]}"} lake env lean --run scripts/conformance/lean/Conformance.lean "$out") \
  >"$runner_log" 2>&1
runner_status=$?
set -e
rg -m 3 '^(MISMATCH|MISSING_EXTERNAL|ERROR)' "$runner_log" || true
tail -n 1 "$runner_log"
echo "runner-log=$runner_log"
echo "runner-wall-seconds=$((SECONDS - runner_start))"
if [[ $pytest_status -ne 0 ]]; then
  exit "$pytest_status"
fi
exit "$runner_status"
