#!/usr/bin/env bash
# Build every project module and reject Lean's hasSorry diagnostic explicitly.
# Lean 4.30 exits successfully for warnings, including declarations discarded
# from the environment (for example `example : False := by sorry`), so the
# environment audit alone cannot cover this case.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
build_log="$(mktemp "${TMPDIR:-/tmp}/verified-fast-confirmation-build.XXXXXX")"
cleanup() {
  rm -f -- "$build_log"
}
trap cleanup EXIT

cd "$repo_root"
build_start=$SECONDS
set +e
lake --no-ansi build 2>&1 | tee "$build_log"
pipeline_status=("${PIPESTATUS[@]}")
set -e
build_status=${pipeline_status[0]}
tee_status=${pipeline_status[1]}

# Pinned Lean 4.30 emits: "declaration uses `sorry`". Match quote-agnostically
# so a cosmetic quote change cannot silently weaken the gate.
set +e
grep -Eq 'declaration uses .sorry.' "$build_log"
grep_status=$?
set -e
if ((grep_status == 0)); then
  echo "build emitted Lean's hasSorry diagnostic" >&2
  exit 1
elif ((grep_status != 1)); then
  echo "could not inspect Lean build diagnostics" >&2
  exit "$grep_status"
fi
if ((tee_status != 0)); then
  echo "could not capture complete Lean build diagnostics" >&2
  exit "$tee_status"
fi
if ((build_status != 0)); then
  exit "$build_status"
fi
echo "Lean build passed without proof placeholders (wall $((SECONDS - build_start))s)"
