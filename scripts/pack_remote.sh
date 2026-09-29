#!/usr/bin/env bash
# Pack everything needed to run the checker on a machine without elan/lake:
# the Lean toolchain, the compiled libraries of the project and its dependencies, the cvc5
# plugin, the checker and its scripts, and the selected benchmarks.
#   scripts/pack_remote.sh [output.tar.gz]
# On the remote machine (same architecture, Linux x86_64):
#   tar xzf checker.tar.gz && cd checker
#   export LEAN_HOME=$PWD/toolchain      # or put toolchain/bin on PATH
#   scripts/check_all.sh --base benchmarks/univariate benchmarks/univariate/list.txt > fine.csv
#   scripts/check_all.sh --coarse --base benchmarks/univariate benchmarks/univariate/list.txt > coarse.csv
set -euo pipefail
cd "$(dirname "$0")/.."
out="$(realpath "${1:-checker.tar.gz}")"
toolchain="$(dirname "$(dirname "$(readlink -f "$(command -v lean)")")")"
stage="$(mktemp -d)"
trap 'rm -rf "$stage"' EXIT
mkdir -p "$stage/checker"
# toolchain (binaries + core oleans)
cp -a "$toolchain" "$stage/checker/toolchain"
# compiled libraries: only lib/lean (oleans) of each package and of the project
for d in .lake/build/lib/lean .lake/packages/*/.lake/build/lib/lean; do
  mkdir -p "$stage/checker/$d"
  cp -a "$d/." "$stage/checker/$d/"
done
# cvc5 plugin
so="$(find .lake/packages/cvc5/.lake -name 'libcvc5_cvc5.so' | head -1)"
mkdir -p "$stage/checker/$(dirname "$so")"
cp -a "$so" "$stage/checker/$so"
# checker sources (for reference), scripts, benchmarks
cp -a Checker.lean scripts "$stage/checker/"
mkdir -p "$stage/checker/benchmarks"
cp -a benchmarks/univariate "$stage/checker/benchmarks/"
tar -C "$stage" -czf "$out" checker
echo "wrote $out ($(du -sh "$out" | cut -f1))"
