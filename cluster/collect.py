#!/usr/bin/env python3
"""Turn the results JSON of a submit-job run (gzipped JSONL written by the job aggregator) into
the outputs of our two experiments.

  cluster/collect.py gen   RESULTS.json.gz [...] --out DIR
      Rebuild the univariate cells printed by cluster/gen_one.sh as DIR/<problem>_<i>.smt2,
      dropping bodies already seen (cross-problem deduplication, provenance comment ignored),
      and write DIR/manifest.csv: problem,result,emitted,nonlinear,kept,merged,termination.

  cluster/collect.py check RESULTS.json.gz [...] > results.csv
      One CSV line per task of a checker run (cluster/check_one.sh):
      file,status,solve_ms,reconstruct_ms,kernel_ms,cputime_s,walltime_s,memory_mb,termination.

RESULTS files can be gzipped (results.json.gz) or already decompressed (results.json); the format
is detected from the file contents, not the name. A gzipped results file whose run is still
going is a stream without its end; the records read so far are used.
"""
import csv, gzip, hashlib, json, os, re, sys, zlib

def open_results(p):
    """Open a results file as text, gzipped or plain."""
    with open(p, "rb") as f:
        gzipped = f.read(2) == b"\x1f\x8b"
    if gzipped:
        return gzip.open(p, "rt", encoding="utf-8")
    return open(p, "r", encoding="utf-8")

def records(paths):
    for p in paths:
        with open_results(p) as f:
            try:
                for line in f:
                    line = line.strip()
                    if line:
                        try:
                            yield json.loads(line)
                        except json.JSONDecodeError:
                            pass  # a partially written last line
            except (EOFError, zlib.error, OSError):
                print(f"note: {p} is incomplete (run still going?); using the records read", file=sys.stderr)

def run_value(run_log, key):
    m = re.search(rf"^{key}=(.*)$", run_log or "", re.M)
    return m.group(1).strip() if m else ""

def termination(run_log):
    return run_value(run_log, "terminationreason") or ("done" if "c done" in (run_log or "") else "")

# direct: refutations of a level by the input constraints alone (each is a candidate cell);
# skip_*: candidates dropped by cvc5 (non-rational lower sample, a constraint became constant,
# same cell as before). Empty when the cvc5 build predates these diagnostics.
DIAG_COLUMNS = ["direct", "skip_nonrational", "skip_constant", "skip_duplicate"]

def gen(paths, out):
    os.makedirs(out, exist_ok=True)
    seen = set()
    rows = []
    for r in records(paths):
        if r.get("type") != "task":
            continue
        log = r.get("output_log") or ""
        problem = r.get("job_args", "")
        m = re.search(r"^\[file\] (.*)$", log, re.M)
        if m:
            problem = m.group(1).strip()
        gen_line = (re.search(r"^\[gen\] (.*)$", log, re.M) or [None, ""])[1]
        if gen_line.startswith("result=error:"):
            # gen_one.sh failed loudly: keep its message as the result
            stats = {"result": gen_line[len("result="):].strip()}
        else:
            stats = dict(re.findall(r"(\w+)=(\S+)", gen_line))
        merged = 0
        for name, body in re.findall(r"^\[cell\] (\S+)\n(.*?)^\[endcell\]$", log, re.M | re.S):
            key = hashlib.md5("".join(l for l in body.splitlines(True) if not l.startswith(";;")).encode()).hexdigest()
            if key in seen:
                continue
            seen.add(key)
            with open(os.path.join(out, name), "w") as f:
                f.write(body)
            merged += 1
        rows.append([problem, stats.get("result", "killed"), stats.get("emitted", ""), stats.get("nonlinear", ""),
                     stats.get("kept", ""), merged]
                    + [stats.get(k, "") for k in DIAG_COLUMNS] + [termination(r.get("run_log"))])
    with open(os.path.join(out, "manifest.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["problem", "result", "emitted", "nonlinear", "kept", "merged"] + DIAG_COLUMNS + ["termination"])
        w.writerows(sorted(rows))
    print(f"{len(rows)} tasks, {len(seen)} distinct cells written to {out}", file=sys.stderr)

def check(paths):
    w = csv.writer(sys.stdout)
    w.writerow(["file", "status", "solve_ms", "reconstruct_ms", "kernel_ms", "cputime_s", "walltime_s", "memory_mb", "termination"])
    for r in records(paths):
        if r.get("type") != "task":
            continue
        log = r.get("output_log") or ""
        run = r.get("run_log") or ""
        def t(k):
            m = re.search(rf"^\[time\] {k}: (\d+)", log, re.M)
            return m.group(1) if m else ""
        m = re.search(r"^\[result\] (.*)$", log, re.M)
        status = m.group(1).strip() if m else "failed"
        term = termination(run)
        if term in ("cputime", "walltime"):
            status = "timeout"
        elif term == "memory":
            status = "memout"
        mem = run_value(run, "memory").rstrip("B")
        w.writerow([r.get("job_args", ""), status, t("solve"), t("reconstruct"), t("kernel"),
                    run_value(run, "cputime").rstrip("s"), run_value(run, "walltime").rstrip("s"),
                    f"{int(mem) / 1048576:.0f}" if mem.isdigit() else "", term])

if __name__ == "__main__":
    if len(sys.argv) < 3 or sys.argv[1] not in ("gen", "check"):
        print(__doc__, file=sys.stderr); sys.exit(2)
    mode, args = sys.argv[1], sys.argv[2:]
    if mode == "gen":
        if "--out" not in args:
            print("gen needs --out DIR", file=sys.stderr); sys.exit(2)
        i = args.index("--out"); out = args[i + 1]; paths = args[:i] + args[i + 2:]
        gen(paths, out)
    else:
        check(args)
