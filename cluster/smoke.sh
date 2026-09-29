#!/usr/bin/bash
# Smoke test for the univariate benchmark generator on the cluster: runs cvc5 on one problem,
# keeps the cells in the task's private /tmp and prints them on stdout (collected in the results
# JSON). Fails loudly when anything prevents the cells from being written.
#   submit-job.sh -d test_one -b one -p quad -w -t 130 -m 8000 --no-copy-bin -- smoke.sh

CVC5=/barrett/scratch/tomaz1502/cvc5/build/bin/cvc5

fail() {
  echo "SMOKE ERROR: $*"
  echo "SMOKE ERROR: $*" >&2
  exit 1
}

[[ -x "$CVC5" ]] || fail "cvc5 not found or not executable at $CVC5"
out="$(mktemp -d 2>/dev/null)" || fail "mktemp failed (TMPDIR='${TMPDIR:-/tmp}')"
[[ -d "$out" && -w "$out" ]] || fail "temporary directory $out is not writable"
trap 'rm -rf "$out" "$out.log"' EXIT
touch "$out/.probe" 2>/dev/null || fail "cannot create files in $out"
rm -f "$out/.probe"
echo "cells directory: $out"

"$CVC5" --nl-ext=none --nl-cov --nl-cov-univ-bench-dir="$out" "$1" > "$out.log" 2>&1
echo "cvc5 exit code: $?"
cat "$out.log"
grep -q 'for writing a univariate benchmark' "$out.log" && fail "cvc5 could not write its cells"
rm -f "$out.log"

n=$(ls "$out" | wc -l)
echo "cells written: $n"
for f in "$out"/*.smt2; do
  [[ -e "$f" ]] || break
  echo "=== $(basename "$f")"
  cat "$f"
done
