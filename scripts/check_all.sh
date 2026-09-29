#!/usr/bin/env bash
# Run the checker on every SMT-LIB file listed in a file (one path per line, absolute or relative
# to a base directory) and write one CSV line per problem:
#   file,status,solve_ms,reconstruct_ms,kernel_ms
#   scripts/check_all.sh [--coarse] [--native] [--solver-opt name=value] [--base DIR] [--timeout SECONDS] list.txt > results.csv
set -uo pipefail
cd "$(dirname "$0")/.."
opts=(); base=""; tmo=600
while [[ $# -gt 1 ]]; do
  case "$1" in
    --coarse|--native) opts+=("$1") ;;
    --solver-opt) opts+=("$1" "$2"); shift ;;
    --base) base="$2"; shift ;;
    --timeout) tmo="$2"; shift ;;
    *) echo "unknown option: $1" >&2; exit 2 ;;
  esac
  shift
done
# list="$1"
echo "file,status,solve_ms,reconstruct_ms,kernel_ms"
for f in $base/*.smt2 ; do
  [[ -z "$f" || "$f" == \#* ]] && continue
  path="$f"
  out="$(timeout "$tmo" scripts/check_smt2.sh "${opts[@]}" "$path" 2>&1)"; code=$?
  status="$(echo "$out" | grep -m1 '^\[result\]' | sed 's/^\[result\] //')"
  [[ $code -eq 124 ]] && status="timeout"
  [[ -z "$status" ]] && status="failed"
  solve="$(echo "$out" | grep -m1 '^\[time\] solve:' | sed 's/ms$//' | sed 's/ms$//' | grep -o '[0-9]*$')"
  recon="$(echo "$out" | grep -m1 '^\[time\] reconstruct:' | sed 's/ms$//' | sed 's/ms$//' | grep -o '[0-9]*$')"
  kern="$(echo "$out" | grep -m1 '^\[time\] kernel:' | sed 's/ms$//' | sed 's/ms$//' | grep -o '[0-9]*$')"
  echo "$f,\"$status\",${solve:-},${recon:-},${kern:-}"
done
