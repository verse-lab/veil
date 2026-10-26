#!/usr/bin/env python3
"""Run the evaluation: build and time the compiled model checkers of the 20 benchmarks in
Examples/TLA, using the instances in their EVAL blocks.
They are named as for TLC (Benchmarks/TLA/scripts/run_all.py), so that the results of both line up.

  1. scripts/bench-model-check-prepare.py writes the evaluation version of each benchmark to
     OUT/specs/<name>.lean: its TEST ONLY checks and its `#gen_executable` deleted, so that
     `#model_check` extracts the executable definitions itself and their extraction is timed,
     and its `/- EVAL ... -/` blocks uncommented.
  2. scripts/bench-model-check.py elaborates and compiles each of them once (compilation timed),
     then runs its checker binary --repeat times at each thread count.
  3. At the end, it runs scripts/bench-model-check-report.py, which prints the tables (medians)
     and writes the CSVs.

OUT is benchmark-results/<name>, unless --out gives another directory in the checkout, where the
evaluation versions are elaborated; paths are relative to the root of the checkout. The other
arguments go to bench-model-check.py (see its --help), e.g. --only, --bin-dir or --skip-lake-build.
The console output is also saved as OUT/console.log. A run that was interrupted is continued with
--resume (same --name), on the evaluation versions it started with, and with its thread counts and
repetitions unless --threads or --repeat give others; to start it over, e.g. after changing a
benchmark, delete its directory first. --rerun runs benchmarks of a run again, e.g. those that the
report shows with memory paged out: NAME builds the benchmark again and redoes all its runs,
NAME:T1,T2 only its runs at those thread counts; the runs they replace stay in the results, apart.
On macOS, the machine is kept from idle-sleeping meanwhile. A full pass takes hours: 20
benchmarks, 14 thread counts and 3 runs of each.

Memory: the larger benchmarks need much of the machine's memory. When other programs hold much of
it, macOS compresses or swaps out part of a checker's memory, and accessing it then costs system
time; so close memory-hungry programs (or restart the machine) before a run. By default nothing
is done about other programs' memory, but each run records how much memory was free when it
started and its peak footprint, and the report lists the runs whose footprint exceeds their
resident set size by 1 GB or more, with their system time: compressed memory that is rarely
accessed costs little. On request, bench-model-check.py also acts before each run: --free-memory
GB holds that much incompressible data for a moment, which pushes the file cache and idle
programs' pages out of memory; --cooldown SECONDS pauses; and --min-free PERCENT waits, for at
most 5 minutes, until that much of the memory is free.

From anywhere, with Lean's `lake` on PATH:
  python3 scripts/bench-model-check-all.py                    # the run "all", in benchmark-results/all
  python3 scripts/bench-model-check-all.py --threads 12 --name all-12threads
  python3 scripts/bench-model-check-all.py --only 2PC Paxos   # some of the benchmarks
  python3 scripts/bench-model-check-all.py --dry-run          # only prepare and list them
  python3 scripts/bench-model-check-all.py --resume           # continue the run "all"
  python3 scripts/bench-model-check-all.py --rerun 2PC Paxos:14   # run these again in "all"
  python3 scripts/bench-model-check-all.py --clean-binaries --bin-dir benchmark-results/all/bin
  python3 scripts/bench-model-check-report.py benchmark-results/all   # print the tables again
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PREPARE = HERE / "bench-model-check-prepare.py"
BENCH = HERE / "bench-model-check.py"
# name, as for TLC in run_all.py and in its order; file in Examples/TLA
BENCHMARKS = [
    ("Bakery", "Bakery"),
    ("EWD840", "EWD840"),
    ("German", "German"),
    ("KeyValueStore", "KeyValueStore"),
    ("MultiPaxos", "MultiPaxos"),
    ("Mutex", "MutexViolation"),
    ("NOPaxos", "NOPaxos"),
    ("Paxos", "Paxos"),
    ("SimpAllocator", "SimpleAllocator"),
    ("2PC", "TwoPhaseCommit"),
    ("bcastByz", "BcastByz"),
    ("FileLease", "FileBasedLease"),
    ("LeaderlessLog", "LeaderlessLog"),
    ("LeaseGuard", "LeaseGuard"),
    ("TicketSem", "OrderedTicketSemaphore"),
    ("Oswald", "Oswald"),
    ("ParCommits", "ParallelCommits"),
    ("Percolator", "Percolator"),
    ("PAStatic", "ProposerAcceptorStatic"),
    ("TaskClaiming", "TaskClaiming"),
]


def prepare_command(specs: Path) -> list:
    return [sys.executable, str(PREPARE), str(specs),
            *(f"{name}=Examples/TLA/{file}.lean" for name, file in BENCHMARKS)]


def spec_files(specs: Path) -> list:
    """The evaluation versions in `specs`, in the order of BENCHMARKS."""
    return [str(specs / f"{name}.lean") for name, _ in BENCHMARKS]


def tee(command: list, log) -> int:
    """Run `command`, copying its output to the terminal and to `log`; return its exit code."""
    # Unbuffered, so that its output appears as it is printed
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               env=dict(os.environ, PYTHONUNBUFFERED="1"))
    # An interrupt from the terminal also reaches the command, which stops its own processes
    # and exits: until then, keep copying its output.
    previous = signal.signal(signal.SIGINT, signal.SIG_IGN)
    try:
        for line in process.stdout:
            sys.stdout.buffer.write(line)
            sys.stdout.flush()
            log.write(line)
            log.flush()
        code = process.wait()
        # As a shell reports a command that a signal ended
        return 128 - code if code < 0 else code
    finally:
        signal.signal(signal.SIGINT, previous)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter,
                                 allow_abbrev=False)
    ap.add_argument("--name", default="all", help="name of the run (default all)")
    ap.add_argument("--out", help="output directory, in the checkout (default benchmark-results/<name>)")
    ap.add_argument("--threads",
                    help="comma-separated thread counts; 1 is the sequential search (default 1 to 14, or the run's "
                         "with --resume)")
    ap.add_argument("-r", "--repeat", type=int,
                    help="runs per benchmark and thread count; the report takes the median (default 3, or the run's "
                         "with --resume)")
    ap.add_argument("--run-timeout", type=int, default=3600, help="seconds per run, 0 for none (default 3600)")
    ap.add_argument("--resume", action="store_true", help="continue the run --name, on its evaluation versions")
    ap.add_argument("--rerun", nargs="+", metavar="NAME[:THREADS]",
                    help="run these benchmarks of the run --name again (implies --resume): NAME, all its runs, after "
                         "building it again; NAME:T1,T2, its runs at those thread counts")
    ap.add_argument("--dry-run", action="store_true", help="only prepare and list the benchmarks")
    ap.add_argument("--clean-binaries", action="store_true",
                    help="delete the kept binaries, after confirmation (see bench-model-check.py)")
    args, rest = ap.parse_known_args()
    os.chdir(ROOT)
    bench = [sys.executable, str(BENCH)]
    if args.clean_binaries:
        return subprocess.run(bench + ["--clean-binaries", *rest]).returncode
    out = Path(args.out or f"benchmark-results/{args.name}")
    if args.rerun:
        if not (out / "results.json").exists():
            sys.exit(f"--rerun: there is no run {args.name} in {out} to run again")
        args.resume = True
    # A resumed run keeps its thread counts and repetitions, unless they are given
    if not args.resume:
        args.threads = args.threads or ",".join(map(str, range(1, 15)))
        args.repeat = 3 if args.repeat is None else args.repeat
    settings = ((["--threads", args.threads] if args.threads else [])
                + (["--repeat", str(args.repeat)] if args.repeat is not None else [])
                + ["--run-timeout", str(args.run_timeout), "--name", args.name, "--out", str(out)])

    if args.dry_run:
        # The evaluation versions go to a temporary directory, which must be in the checkout too
        Path("benchmark-results").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix=".dry-run.", dir="benchmark-results") as specs:
            prepared = subprocess.run(prepare_command(Path(specs)))
            if prepared.returncode:
                return prepared.returncode
            return subprocess.run(bench + spec_files(Path(specs)) + settings + ["--dry-run", *rest]).returncode

    if not out.resolve().is_relative_to(ROOT):
        sys.exit(f"{out} is not in the checkout {ROOT}, where its evaluation versions are elaborated")
    # Never replace the evaluation versions that the results of a run were obtained on
    if (out / "results.json").exists() and not args.resume:
        sys.exit(f"{out / 'results.json'} exists; use --resume to continue that run, or another --name")
    if shutil.which("caffeinate"):
        # Until this process exits
        subprocess.Popen(["caffeinate", "-i", "-w", str(os.getpid())])
    out.mkdir(parents=True, exist_ok=True)
    specs = out / "specs"
    with open(out / "console.log", "ab") as log:
        def say(text: str):
            print(text, flush=True)
            log.write(f"{text}\n".encode())
            log.flush()
        setup = (([f"threads {args.threads}"] if args.threads else [])
                 + ([f"{args.repeat} run(s) per benchmark and thread count"] if args.repeat is not None else [])
                 + [f"timeout {args.run_timeout}s per run"])
        say(f"run {args.name}: {', '.join(setup)}; output in {out}"
            + (f"; running again: {' '.join(args.rerun)}" if args.rerun else ""))
        if args.resume and specs.is_dir():
            say(f"resuming on the evaluation versions in {specs}")
        else:
            prepared = tee(prepare_command(specs), log)
            if prepared:
                return prepared
        return tee(bench + spec_files(specs) + settings + (["--resume"] if args.resume else []) + rest
                   + (["--rerun", *args.rerun] if args.rerun else []), log)


if __name__ == "__main__":
    sys.exit(main())
