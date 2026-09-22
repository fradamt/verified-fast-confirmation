#!/usr/bin/env bash
set -u

if [[ $# -ne 4 ]]; then
  echo "usage: scripts/conformance/run.sh <consensus-specs-dir> <fork> <preset> <out.jsonl>" >&2
  exit 2
fi

consensus_specs_dir=$1
fork=$2
preset=$3
out=$4
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
plugin_dir="$repo_root/scripts/conformance/python"
tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/fcr-conformance.XXXXXX")"
trace_base="$tmp_dir/trace.jsonl"
pytest_log="$tmp_dir/pytest.log"
trap 'rm -rf "$tmp_dir"' EXIT

mkdir -p "$(dirname "$out")"
export FCR_TRACE_OUT="$trace_base"
set +e
(
  cd "$consensus_specs_dir" || exit 1
  PYTHONPATH="$plugin_dir${PYTHONPATH:+:$PYTHONPATH}" \
    uv run pytest "tests/core/pyspec/eth_consensus_specs/test/phase0/fast_confirmation" \
      --reftests --fork="$fork" --preset="$preset" -p fcr_trace_plugin
) >"$pytest_log" 2>&1
pytest_status=$?
set -e

shopt -s nullglob
trace_files=("$tmp_dir/trace.jsonl" "$tmp_dir"/trace.*.jsonl)
: >"$out"
if [[ ${#trace_files[@]} -gt 0 ]]; then
  cat "${trace_files[@]}" >>"$out"
fi
record_count=$(wc -l <"$out" | tr -d ' ')
echo "records=$record_count"
if [[ $pytest_status -ne 0 ]]; then
  echo "pytest-status=$pytest_status"
  rg -n "FAILED|ERROR|E   " "$pytest_log" | head -20 || true
fi

if [[ -x "$repo_root/.lake/build/bin/conformance" ]]; then
  echo "runner-summary:"
  "$repo_root/.lake/build/bin/conformance" "$out" | tail -n 1
else
  echo "runner absent"
fi

exit 0
