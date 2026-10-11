#!/usr/bin/env bash
# Cluster entry point for the checker: one SMT-LIB file per invocation, suitable as the
# EXECUTABLE of submit-job (the benchmark path is the last argument).
#   cluster/check_one.sh [--coarse] [--native] [--recompute-sturm] [--solver-opt name=value ...] file.smt2
# Prints [time] solve / reconstruct / kernel and [result] on stdout (captured in output.log).
# Configuration through the environment (all optional):
#   CHECKER_ROOT  the unpacked checker directory (default: the parent of this script's directory)
#   LEAN_HOME     the Lean toolchain (default: $CHECKER_ROOT/toolchain)
#   LOGDIR        writable directory for the driver file (set by runexec; default: a temp dir)
#   CHECK_WARMUP  0 turns off reading the compiled libraries before Lean starts
#   CHECK_COLD_MS warm-up time (ms) above which the machine counts as cold (default 300000): the
#                 checker then runs once with its output discarded (at most CHECK_COLD_RUN_S
#                 seconds, default 300) before the run whose times are reported
set -euo pipefail
here="$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")" && pwd)"
root="${CHECKER_ROOT:-$(dirname "$here")}"
export LEAN_HOME="${LEAN_HOME:-$root/toolchain}"
coarse=false; native=false; sturm_cert=true; opts=""
while [[ $# -gt 1 ]]; do
  case "$1" in
    --coarse) coarse=true ;;
    --native) native=true ;;
    --recompute-sturm) sturm_cert=false ;; # ignore the Sturm sequences shipped by cvc5
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
printf 'import Checker\nrun_cmd Checker.check "%s" (coarse := %s) (native := %s) (sturmCert := %s) (solverOptions := %s)\n' "$file" "$coarse" "$native" "$sturm_cert" "$opts" > "$driver"
echo "[file] $file"
# Read the compiled libraries into the page cache before Lean starts. Lean maps these files and
# reads them lazily, so on a machine where they are not cached yet (a shared filesystem on a
# cluster node) the reads would otherwise stall inside the checker's timed phases.
# CHECK_WARMUP=0 turns this off.
warm_ms=0
if [[ "${CHECK_WARMUP:-1}" != 0 ]]; then
  w0=$(date +%s%N)
  IFS=: read -r -a warm_dirs <<< "$lean_path"
  find "${warm_dirs[@]}" -name '*.olean*' -type f -print0 2>/dev/null | xargs -0 -r cat > /dev/null 2>&1 || true
  cat "$so" > /dev/null 2>&1 || true
  warm_ms=$(( ($(date +%s%N) - w0) / 1000000 ))
  echo "[time] warmup: ${warm_ms}ms"
fi
# A slow warm-up means the machine was cold, and the other tasks that started on it at the same
# time are still loading the same files: even after the warm-up, the checker's timed phases were
# measured to be inflated on such machines. Run the checker once and discard its output, so that
# the run below is a warm one.
if (( warm_ms > ${CHECK_COLD_MS:-300000} )); then
  c0=$(date +%s%N)
  LEAN_PATH="$lean_path" timeout "${CHECK_COLD_RUN_S:-300}" "$LEAN_HOME/bin/lean" -j 1 --plugin="$so" "$driver" \
    > "$work/discarded_run.log" 2>&1 || true
  echo "[time] discarded-cold-run: $(( ($(date +%s%N) - c0) / 1000000 ))ms"
fi
# Time this task spent stalled on I/O during the reported run, from the "some" line of its
# cgroup's pressure file (cgroup v2 with PSI; not printed when the file is not readable).
pressure="/sys/fs/cgroup$(sed -n 's/^0:://p' /proc/self/cgroup 2>/dev/null)/io.pressure"
io_us() { awk '/^some/ { for (i = 2; i <= NF; i++) if (sub(/^total=/, "", $i)) print $i }' "$pressure" 2>/dev/null; }
s0=$(io_us || true)
rc=0
LEAN_PATH="$lean_path" "$LEAN_HOME/bin/lean" -j 1 --plugin="$so" "$driver" || rc=$?
s1=$(io_us || true)
if [[ -n "$s0" && -n "$s1" ]]; then echo "[time] io_stall: $(( (s1 - s0) / 1000 ))ms"; fi
exit "$rc"
