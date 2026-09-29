# Running the experiments on the cluster

Everything here is driven by `submit-job` (one SLURM array task per line of a
`benchmark_set_<name>` file, run under `runexec` with a time and memory limit; stdout of each
task lands in `<workdir>/<set>/<benchmark>/output.log`, resource usage in `run.out`).
Option names below are those of the Python `submit-job.sh` (`--help` of 2026-09-28). Two points
specific to it: per-job log directories, which the wrappers rely on (`$LOGDIR`), are created
only with `--log-dirs`; and there is no `-o` option, so arguments for the executable are given
after it, following `--`, and the benchmark path is appended as the last argument.

## Setup on the cluster

Cluster facts that matter (CENTAUR introduction slides, 2024-11-18): compute nodes run Ubuntu
20.04 (glibc 2.31), turbo boost is disabled, each task gets its own /tmp and exclusive node
access; `/barrett/scratch/<user>` is the working area (home is on AFS with little space, do not
put runs there); high-throughput jobs belong on octa/amd; do not mix partitions within one
comparison, so run fine and coarse on the same partition; `cmpr.py` in
`/barrett/scratch/local/bin` extracts runexec data from a working directory (`--csv`).

1. Unpack the checker archive built by `scripts/pack_remote.sh` (toolchain, compiled libraries,
   plugin, `Checker.lean`, scripts, `benchmarks/univariate`), e.g. into `/barrett/scratch/tomaz1502/checker`.
   `cluster/check_one.sh` finds everything relative to that directory
   (`CHECKER_ROOT`, `LEAN_HOME=$CHECKER_ROOT/toolchain`).
2. Build the instrumented cvc5 (branch with `--nl-cov-univ-bench-dir`) and export `CVC5` with
   its path, or put it on `PATH`.
3. Write the benchmark set files, one absolute path per line, newline-terminated:
   - `benchmark_set_univ`: the 78 univariate problems (`benchmarks/univariate/list.txt` with the
     directory prefix);
   - `benchmark_set_hard`: the 2547 multivariate problems for the generator.

## Portability warning (checker only)

The compute nodes run glibc 2.31 (Ubuntu 20.04). The Lean toolchain needs only glibc 2.17, but
the cvc5 plugin `libcvc5_cvc5.so` is linked from the static archives of the GitHub release,
which are built on Ubuntu 24.04: `libcvc5.a` and `libgmp.a` reference `__isoc23_strtol`
(glibc 2.38) and `libcadical.a` references `stat`/`fstat` as real symbols (glibc 2.33). A plugin
linked from them does not load on the nodes. Options, to be settled on the cluster:
- build cvc5 (static, libc++) and the plugin on barrett2 itself, which needs a C++ compiler
  with libc++ headers there; or a libstdc++ build with an adapted lean-cvc5 lakefile;
- run the checker inside an Apptainer/Singularity image of a recent distribution
  (`docker://debian:13`), if the nodes provide it and it works under runexec.
The generator (`gen_one.sh`) is unaffected: it uses the cvc5 compiled on the cluster.

## 1. Generate univariate cells from the multivariate problems

Inside a task, `LOGDIR` is empty, the working directory is the run directory, and everything
except the task's private `/tmp` is read-only (found with a probe run on 2026-09-29). So
`gen_one.sh` keeps cvc5's raw cells in `/tmp` and prints the kept cells on stdout, which the job
aggregator stores in the run's results JSON; no `--log-dirs` needed.

    export CVC5=/barrett/scratch/tomaz1502/cvc5/build/bin/cvc5
    submit-job.sh -d gen_run -b hard -p quad -w -t 130 -m 8000 --no-copy-bin \
        -- /barrett/scratch/tomaz1502/checker/cluster/gen_one.sh --cap 100 --timeout 110

If `CVC5` is not passed through to the task, hard-code the path in `gen_one.sh`. When the run is
over, rebuild the cells, with cross-problem deduplication:

    /barrett/scratch/tomaz1502/checker/cluster/collect.py gen <results>.json.gz --out generated
    # generated/*.smt2 and generated/manifest.csv
    ls $PWD/generated/*.smt2 > benchmark_set_generated

`collect.py` also reads an unfinished results file (the aggregator closes the gzip stream only
when all tasks are done), using the records written so far.

## 2. Check the proofs (fine-grained and coarse)

    submit-job.sh -d check_fine   -b "univ generated" -p quad -c 2 -w -t 600 -m 16000 --no-copy-bin \
        /barrett/scratch/tomaz1502/checker/cluster/check_one.sh
    submit-job.sh -d check_coarse -b "univ generated" -p quad -c 2 -w -t 600 -m 16000 --no-copy-bin \
        /barrett/scratch/tomaz1502/checker/cluster/check_coarse_one.sh

Both must run on the same partition. `check_one.sh` writes its driver file to `/tmp` and prints
`[time] solve`, `[time] reconstruct`, `[time] kernel` (ms) and `[result]`. Then:

    /barrett/scratch/tomaz1502/checker/cluster/collect.py check <fine results>.json.gz   > fine.csv
    /barrett/scratch/tomaz1502/checker/cluster/collect.py check <coarse results>.json.gz > coarse.csv

(columns: file,status,solve_ms,reconstruct_ms,kernel_ms,cputime_s,walltime_s,memory_mb,termination;
runexec's time/memory limits are reported as `timeout`/`memout`).

## Notes

- `--no-copy-bin` matters: the wrappers locate the checker/toolchain relative to their own path.
- The octa partition was saturated on 2026-09-29; quad worked.
- The probe task ran on barrett3 with an Ubuntu 24.04 kernel (6.8.0-63, `#66-Ubuntu`), not the
  Ubuntu 20.04 of the 2024 slides; if the nodes are on 24.04 (glibc 2.39), the plugin
  portability warning above does not apply. Confirm with a task running `ldd --version`.
