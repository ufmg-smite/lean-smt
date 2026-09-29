#!/usr/bin/env bash
# Cluster entry point for the checker: one SMT-LIB file per invocation, suitable as the
# EXECUTABLE of submit-job (the benchmark path is the last argument).
#   cluster/check_one.sh [--coarse] [--native] [--solver-opt name=value ...] file.smt2
# Prints [time] solve / reconstruct / kernel and [result] on stdout (captured in output.log).
# Configuration through the environment (all optional):
#   CHECKER_ROOT  the unpacked checker directory (default: the parent of this script's directory)
#   LEAN_HOME     the Lean toolchain (default: $CHECKER_ROOT/toolchain)
#   LOGDIR        writable directory for the driver file (set by runexec; default: a temp dir)
set -euo pipefail
here="$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")" && pwd)"
root="${CHECKER_ROOT:-$(dirname "$here")}"
export LEAN_HOME="${LEAN_HOME:-$root/toolchain}"
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
file="$(readlink -f "$1")"
so="$(find "$root/.lake/packages/cvc5/.lake" -name 'libcvc5_cvc5.so' | head -1)"
lean_path="$root/.lake/build/lib/lean"
for d in "$root"/.lake/packages/*/.lake/build/lib/lean; do lean_path="$lean_path:$d"; done
lean_path="$lean_path:$LEAN_HOME/lib/lean"
work="${LOGDIR:-$(mktemp -d)}"
driver="$work/driver.lean"
printf 'import Checker\nrun_cmd Checker.check "%s" (coarse := %s) (native := %s) (solverOptions := %s)\n' "$file" "$coarse" "$native" "$opts" > "$driver"
echo "[file] $file"
LEAN_PATH="$lean_path" "$LEAN_HOME/bin/lean" -j 1 --plugin="$so" "$driver"
