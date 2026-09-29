#!/usr/bin/env python3
"""Stratified sample of a list of QF_NRA problems.

  scripts/sample_gen.py [--n 50] [--seed 0] LIST OUT

LIST holds benchmark paths, one per line. Problems are grouped by family: the top directory, or
for meti-tarski, which is most of SMT-LIB QF_NRA, its second-level directory. The sample takes one
random problem per group in turn, round-robin over the groups in random order, until N problems
are chosen, so every group is represented before any group gets a second problem. The seed makes
the sample reproducible. The sample is written to OUT, one path per line, in the input's format;
a summary per group goes to stderr.
"""
import argparse, random, sys
from collections import defaultdict

def group_of(path):
    parts = path.strip("/").split("/")
    # tolerate absolute paths: start at the component after QF_NRA if present
    if "QF_NRA" in parts:
        parts = parts[len(parts) - 1 - parts[::-1].index("QF_NRA") + 1:]
    if parts and parts[0] == "meti-tarski" and len(parts) > 2:
        return "/".join(parts[:2])
    return parts[0] if parts else ""

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=50)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("list")
    ap.add_argument("out")
    a = ap.parse_args()

    problems = [l.strip() for l in open(a.list) if l.strip()]
    groups = defaultdict(list)
    for p in problems:
        groups[group_of(p)].append(p)
    rng = random.Random(a.seed)
    order = sorted(groups)
    rng.shuffle(order)
    pools = {g: rng.sample(groups[g], len(groups[g])) for g in order}
    target = min(a.n, len(problems))
    sample = []
    while len(sample) < target:
        for g in order:
            if pools[g] and len(sample) < target:
                sample.append(pools[g].pop())
    with open(a.out, "w") as f:
        f.write("".join(p + "\n" for p in sample))

    picked = defaultdict(int)
    for p in sample:
        picked[group_of(p)] += 1
    print(f"{len(problems)} problems in {len(groups)} groups; sampled {len(sample)} into {a.out}",
          file=sys.stderr)
    for g in sorted(groups, key=lambda g: -len(groups[g])):
        print(f"  {picked[g]:3d} of {len(groups[g]):5d}  {g}", file=sys.stderr)

if __name__ == "__main__":
    main()
