#!/usr/bin/env bash
# Check cvc5's proof of an SMT-LIB file with lean-smt (see Checker.lean).
#   scripts/check_smt2.sh [--coarse] [--native] [--solver-opt name=value ...] file.smt2
# Prints [time] solve / reconstruct / kernel (ms) and [result].
#
# Works with or without Lake: if `lake` is not on PATH (e.g. on a machine where only the
# toolchain and the compiled `.lake` directories were copied, see scripts/pack_remote.sh),
# LEAN_PATH is assembled from the `.lake` build directories and `lean` is taken from
# $LEAN_HOME/bin or from PATH.
set -euo pipefail
cd "$(dirname "$0")/.."
coarse=false; native=false; opts=""
while [[ $# -gt 1 ]]; do
  case "$1" in
    --coarse) coarse=true ;;
    --native) native=true ;;
    --solver-opt) # name=value, repeatable: overrides a cvc5 option of the tactic's set
      opts="$opts, (\"${2%%=*}\", \"${2#*=}\")"; shift ;;
    *) echo "unknown option: $1" >&2; exit 2 ;;
  esac
  shift
done
opts="[${opts#, }]"
[[ $# -eq 1 ]] || { echo "usage: $0 [--coarse] [--native] file.smt2" >&2; exit 2; }
file="$(realpath "$1")"
so="$(find .lake/packages/cvc5/.lake -name 'libcvc5_cvc5.so' | head -1)"
driver="$(mktemp --suffix=.lean)"
trap 'rm -f "$driver"' EXIT
printf 'import Checker\nrun_cmd Checker.check "%s" (coarse := %s) (native := %s) (solverOptions := %s)\n' "$file" "$coarse" "$native" "$opts" > "$driver"
if command -v lake > /dev/null 2>&1; then
  lake env lean --plugin="$so" "$driver"
else
  lean_bin="${LEAN_HOME:+$LEAN_HOME/bin/}lean"
  root="$(pwd)"
  lean_path="$root/.lake/build/lib/lean"
  for d in "$root"/.lake/packages/*/.lake/build/lib/lean; do
    lean_path="$lean_path:$d"
  done
  sysroot="$("$lean_bin" --print-prefix)"
  LEAN_PATH="$lean_path:$sysroot/lib/lean" "$lean_bin" --plugin="$so" "$driver"
fi
