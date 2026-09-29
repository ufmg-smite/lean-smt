#!/usr/bin/env bash
# Select the univariate SMT-LIB problems: copy the files listed in a list file (paths relative to
# the QF_NRA benchmark root) into an output directory, keeping their relative paths, and write the
# list there as `list.txt` for `scripts/check_all.sh --base <out> <out>/list.txt`.
#   scripts/filter_univ.sh [list] [benchmark root] [output dir]
set -euo pipefail
cd "$(dirname "$0")/.."
list="${1:-$HOME/Academic/Public/paper-tacas27-univ_coverings/univ_smtlib.txt}"
root="${2:-benchmarks/QF_NRA/non-incremental/QF_NRA}"
out="${3:-benchmarks/univariate}"
mkdir -p "$out"
: > "$out/list.txt"
found=0; missing=0
while read -r f; do
  [[ -z "$f" || "$f" == \#* ]] && continue
  if [[ -f "$root/$f" ]]; then
    mkdir -p "$out/$(dirname "$f")"
    cp "$root/$f" "$out/$f"
    echo "$f" >> "$out/list.txt"
    found=$((found + 1))
  else
    echo "missing: $root/$f" >&2
    missing=$((missing + 1))
  fi
done < "$list"
echo "copied $found problems into $out ($missing missing); list at $out/list.txt"
