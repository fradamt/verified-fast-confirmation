#!/usr/bin/env bash
# Replay every project module through the checker shipped with lean-toolchain.
set -euo pipefail
cd "$(dirname "$0")/.."
mapfile -t modules < <(python3 - <<'PY'
from pathlib import Path
libs = ("FastConfirmationModel", "FastConfirmationStatements",
        "FastConfirmationInternal", "FastConfirmationProofs",
        "FastConfirmationWitnesses")
paths = []
for lib in libs:
    paths.extend(sorted(Path(lib).rglob("*.lean")))
    paths.append(Path(f"{lib}.lean"))
paths.append(Path("FastConfirmation.lean"))
for path in paths:
    print(".".join(path.with_suffix("").parts))
PY
)
batch=()
for module in "${modules[@]}"; do
  if [[ "$module" != *.* ]]; then
    if ((${#batch[@]})); then
      lake env lean --run scripts/KernelReplay.lean "${batch[@]}"
      batch=()
    fi
    lake env lean --run scripts/KernelReplay.lean "$module"
    continue
  fi
  batch+=("$module")
  if ((${#batch[@]} == 4)); then
    lake env lean --run scripts/KernelReplay.lean "${batch[@]}"
    batch=()
  fi
done
if ((${#batch[@]})); then
  lake env lean --run scripts/KernelReplay.lean "${batch[@]}"
fi
echo "kernel replay passed: ${#modules[@]} project modules"
