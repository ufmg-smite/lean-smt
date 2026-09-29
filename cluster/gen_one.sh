#!/usr/bin/env bash
# Cluster entry point for the univariate benchmark generator: one QF_NRA problem per task.
#   cluster/gen_one.sh [--cap N] [--timeout S] [--keep-linear] file.smt2 [-- extra cvc5 options]
#
# Runs the instrumented cvc5 ($CVC5, default `cvc5` on PATH) with --nl-cov --nl-ext=none,
# keeping its raw cells in a private temporary directory (each cluster task has its own /tmp;
# the rest of the filesystem is read-only inside runexec). Linear cells are dropped unless
# --keep-linear, at most N cells are kept (default 100, emission order), and the kept cells are
# printed on stdout, which the job aggregator collects into the run's results JSON:
#   [file] <problem>
#   [cell] <name>.smt2
#   ...cell contents...
#   [endcell]
#   [gen] result=<unsat|sat|unknown|timeout|error> emitted=<n> nonlinear=<n> kept=<n>
# `cluster/collect.py gen` turns the results JSON back into files.
# --timeout S stops cvc5 after S seconds (default 110) so that the cells are still printed;
# give the job a slightly larger limit (e.g. submit-job -w -t 130).
set -uo pipefail
cap=100; keep_linear=false; tmo=110
while [[ $# -gt 0 ]]; do
  case "$1" in
    --cap) cap="$2"; shift 2 ;;
    --timeout) tmo="$2"; shift 2 ;;
    --keep-linear) keep_linear=true; shift ;;
    --) shift; break ;;
    -*) echo "unknown option: $1" >&2; exit 2 ;;
    *) file="$1"; shift ;;
  esac
done
[[ -n "${file:-}" ]] || { echo "usage: $0 [options] file.smt2" >&2; exit 2; }
extra=("$@")
cvc5="${CVC5:-cvc5}"
echo "[file] $file"

# Fail loudly, on stdout (collected by the job aggregator) and on stderr, instead of reporting
# zero cells. Inside a cluster task LOGDIR is empty and everything but /tmp is read-only.
fail() {
  echo "[gen] result=error: $*"
  echo "gen_one.sh: error: $*" >&2
  exit 1
}
command -v "$cvc5" > /dev/null 2>&1 || fail "cvc5 binary '$cvc5' not found or not executable (set CVC5)"
work="$(mktemp -d 2>/dev/null)" || work=""
[[ -n "$work" && -d "$work" && -w "$work" ]] ||
  fail "no writable temporary directory (TMPDIR='${TMPDIR:-/tmp}')"
trap 'rm -rf "$work"' EXIT
raw="$work/raw"
mkdir -p "$raw" 2>/dev/null && touch "$raw/.probe" 2>/dev/null && rm -f "$raw/.probe" ||
  fail "cannot write to the cell directory $raw"
timeout "$tmo" "$cvc5" --nl-cov --nl-ext=none --nl-cov-univ-bench-dir="$raw" "${extra[@]}" "$file" \
  > "$work/cvc5.out" 2>&1
code=$?
# cvc5 only warns when it cannot write a cell and then goes on; treat that as an error
if grep -q 'for writing a univariate benchmark' "$work/cvc5.out"; then
  fail "cvc5 could not write cells: $(grep -m1 'for writing a univariate benchmark' "$work/cvc5.out")"
fi
res="$(grep -m1 -xE 'sat|unsat|unknown' "$work/cvc5.out")"
if [[ $code -eq 124 ]]; then res="timeout"; elif [[ -z "$res" ]]; then res="error"; fi
if [[ "$res" == "error" ]]; then
  echo "[cvc5]"; head -20 "$work/cvc5.out"; echo "[endcvc5]"
fi
emitted=$(ls "$raw" | wc -l)
name="$(basename "$file" .smt2)"
nonlin=0; kept=0
for g in $(ls "$raw" | sed -E 's/^(.*)_([0-9]+)\.smt2$/\2 \1_\2.smt2/' | sort -n | cut -d' ' -f2); do
  if ! $keep_linear && ! grep -q '(\* x x' "$raw/$g"; then continue; fi
  nonlin=$((nonlin + 1))
  [[ $kept -ge $cap ]] && continue
  echo "[cell] ${name}_$kept.smt2"
  cat "$raw/$g"
  echo "[endcell]"
  kept=$((kept + 1))
done
# what happened to the direct refutations (cvc5 prints one "univ-bench:" line per refutation and
# one per dropped cell; older cvc5 builds print none, then these counts are all 0)
count() { grep -c "univ-bench: $1" "$work/cvc5.out"; }
echo "[gen] result=$res emitted=$emitted nonlinear=$nonlin kept=$kept" \
  "direct=$(count 'direct cover') skip_nonrational=$(count 'skip nonrational')" \
  "skip_constant=$(count 'skip constant') skip_duplicate=$(count 'skip duplicate')"
