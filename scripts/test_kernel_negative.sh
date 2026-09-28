#!/usr/bin/env bash
# A forged theorem can compile with skipKernelTC; replay must reject its olean.
set -euo pipefail
cd "$(dirname "$0")/.."
scratch="$(mktemp -d "${TMPDIR:-/tmp}/fcr-kernel-negative.XXXXXX")"
trap 'rm -rf -- "$scratch"' EXIT
cat > "$scratch/TrustForgery.lean" <<'LEAN'
module
import Lean
open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl (Declaration.thmDecl
  { name := `TrustForgery.bogus, levelParams := [],
    type := mkConst ``False, value := mkConst ``True.intro })
LEAN
lake env bash -c '
  set -euo pipefail
  export LEAN_PATH="$1:${LEAN_PATH:-}"
  # Lean infers the module name from the working folder, so compile there.
  if ! (cd "$1" && lean -o TrustForgery.olean TrustForgery.lean) > "$1/build.out" 2>&1; then
    cat "$1/build.out" >&2
    echo "the forged module did not compile; the test cannot run" >&2
    exit 1
  fi
  if [[ ! -s "$1/TrustForgery.olean" ]]; then
    echo "the forged object file is absent; the test cannot run" >&2
    exit 1
  fi
  if lean --run scripts/KernelReplay.lean TrustForgery > "$1/replay.out" 2>&1; then
    echo "kernel replay accepted skipKernelTC forgery" >&2
    exit 1
  fi
  # The kernel must reject the forged declaration itself, not fail for
  # another reason such as a missing object file.
  if ! grep -q "declaration type mismatch, .TrustForgery.bogus." "$1/replay.out"; then
    cat "$1/replay.out" >&2
    echo "checker failed for an unrelated reason" >&2
    exit 1
  fi
' bash "$scratch"
echo "negative kernel replay passed: skipKernelTC forgery rejected"
