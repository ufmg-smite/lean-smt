#!/usr/bin/env bash
# Generate univariate benchmarks from a list of multivariate QF_NRA problems, with the
# instrumented cvc5 (option --nl-cov-univ-bench-dir, ~/Projects/cvc5/ufmg-smite/gen_univ_benchmarks).
#
#   scripts/gen_univ.sh [--base DIR] [--out DIR] [--cap N] [--timeout S] [--keep-linear] \
#                       list.txt [-- extra cvc5 options]
#
# For each problem in list.txt (paths relative to --base, default the QF_NRA directory), cvc5 is
# run with a time limit and the subproblems it refutes directly are collected. Post-processing:
#   - files with no nonlinear term in x are dropped (unless --keep-linear),
#   - at most N files per source problem are kept (default 50, in emission order),
#   - files whose body (without the provenance comment) was already produced by an earlier
#     problem are dropped.
# Output: OUT/<family>/<problem>_<i>.smt2 and OUT/manifest.csv
#   file,source,solver_result,emitted,kept_after_linear_filter,kept
# The cvc5 binary is $CVC5 or the gen_univ_benchmarks build.
set -uo pipefail
cd "$(dirname "$0")/.."
base="benchmarks/QF_NRA/non-incremental/QF_NRA"; out="benchmarks/generated"; cap=50; tmo=60; keep_linear=false
while [[ $# -gt 0 ]]; do
  case "$1" in
    --base) base="$2"; shift 2 ;;
    --out) out="$2"; shift 2 ;;
    --cap) cap="$2"; shift 2 ;;
    --timeout) tmo="$2"; shift 2 ;;
    --keep-linear) keep_linear=true; shift ;;
    --) shift; break ;;
    -*) echo "unknown option: $1" >&2; exit 2 ;;
    *) list="$1"; shift ;;
  esac
done
[[ -n "${list:-}" ]] || { echo "usage: $0 [options] list.txt [-- cvc5 options]" >&2; exit 2; }
extra=("$@")
cvc5="${CVC5:-$HOME/Projects/cvc5/ufmg-smite/gen_univ_benchmarks/build/bin/cvc5}"
mkdir -p "$out"
manifest="$out/manifest.csv"
echo "file,source,solver_result,emitted,kept_after_linear_filter,kept" > "$manifest"
declare -A seen
total=0
while read -r f; do
  [[ -z "$f" || "$f" == \#* ]] && continue
  src="$base/$f"
  [[ -f "$src" ]] || { echo "missing: $src" >&2; continue; }
  fam="$(dirname "$f" | cut -d/ -f1)"
  name="$(basename "$f" .smt2)"
  tmp="$(mktemp -d)"
  res="$(timeout "$tmo" "$cvc5" --nl-cov --nl-cov-univ-bench-dir="$tmp" "${extra[@]}" "$src" 2>&1 | head -1)"
  [[ -z "$res" || "$res" == *SIGTERM* ]] && res="timeout"
  emitted=$(ls "$tmp" | wc -l)
  # emission order: the counter in the file name
  files=$(ls "$tmp" | sed -E 's/^(.*)_([0-9]+)\.smt2$/\2 \1_\2.smt2/' | sort -n | cut -d' ' -f2)
  nonlin=0; kept=0
  mkdir -p "$out/$fam"
  for g in $files; do
    if ! $keep_linear && ! grep -q '(\* x x' "$tmp/$g"; then continue; fi
    nonlin=$((nonlin + 1))
    [[ $kept -ge $cap ]] && continue
    h="$(grep -v '^;;' "$tmp/$g" | md5sum | cut -d' ' -f1)"
    [[ -n "${seen[$h]:-}" ]] && continue
    seen[$h]=1
    cp "$tmp/$g" "$out/$fam/${name}_$kept.smt2"
    kept=$((kept + 1))
  done
  rm -rf "$tmp"
  total=$((total + kept))
  echo "$f,$res,$emitted,$nonlin,$kept" | sed "s|^|$fam/$name,|" >> "$manifest"
  printf "%-60s %-8s emitted=%-5d nonlinear=%-5d kept=%d\n" "$f" "$res" "$emitted" "$nonlin" "$kept" >&2
done < "$list"
echo "kept $total benchmarks in $out (manifest: $manifest)" >&2
