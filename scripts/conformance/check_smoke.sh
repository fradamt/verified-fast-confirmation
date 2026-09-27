#!/usr/bin/env bash
set -euo pipefail

repo=$1
root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$root"
python3 scripts/check_consensus_source.py --repo "$repo"
export PYTHONPATH="$repo/tests/core/pyspec${PYTHONPATH:+:$PYTHONPATH}"
temp="$(mktemp -d)"
trap 'rm -rf "$temp"' EXIT
examples=scripts/conformance/lean/examples
for name in genesis-ok safe-execution-ok; do
  python3 scripts/conformance/python/check_trace.py "$examples/$name.jsonl"
  lake env lean --run scripts/conformance/lean/Conformance.lean "$examples/$name.jsonl"
done
python3 - "$examples/genesis-ok.jsonl" "$temp/wrong-pin.jsonl" <<'PY'
import json
import sys
record = json.loads(open(sys.argv[1], encoding='utf-8').read())
record['source_pin'] = '0' * 40
with open(sys.argv[2], 'w', encoding='utf-8') as output:
    output.write(json.dumps(record) + '\n')
PY
if python3 scripts/conformance/python/check_trace.py "$temp/wrong-pin.jsonl" >"$temp/wrong-pin.schema" 2>&1 ||
   ! grep -q 'wrong source pin' "$temp/wrong-pin.schema"; then
  echo "trace schema accepted a wrong source pin" >&2
  exit 1
fi
if lake env lean --run scripts/conformance/lean/Conformance.lean "$temp/wrong-pin.jsonl" >"$temp/wrong-pin.lean" 2>&1 ||
   ! grep -q 'wrong source pin' "$temp/wrong-pin.lean"; then
  echo "Lean trace reader accepted a wrong source pin" >&2
  exit 1
fi
for name in genesis-wrong safe-execution-wrong historical-v1; do
  if [[ "$name" == historical-v1 ]]; then
    if python3 scripts/conformance/python/check_trace.py "$examples/$name.jsonl" >"$temp/$name.schema" 2>&1 ||
       ! grep -q 'schema v1' "$temp/$name.schema"; then
      echo "historical schema check did not reject v1" >&2
      exit 1
    fi
  else
    python3 scripts/conformance/python/check_trace.py "$examples/$name.jsonl" >"$temp/$name.schema"
  fi
  if lake env lean --run scripts/conformance/lean/Conformance.lean "$examples/$name.jsonl" >"$temp/$name.lean" 2>&1; then
    echo "negative trace was accepted: $name" >&2
    exit 1
  fi
  if [[ "$name" == historical-v1 ]]; then
    grep -q 'schema v1' "$temp/$name.lean"
  else
    grep -q '^MISMATCH ' "$temp/$name.lean"
  fi
done
"$repo/.venv/bin/python" scripts/conformance/python/gloas_helper_observations.py \
  --consensus-repo "$repo" --out "$temp/helpers.json"
lake env lean --run scripts/conformance/lean/GloasHelpers.lean "$temp/helpers.json"
