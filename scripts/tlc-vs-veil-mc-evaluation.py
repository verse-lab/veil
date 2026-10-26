#!/usr/bin/env python3
"""Run the whole evaluation: TLC on the 20 TLA+ benchmarks, Veil on their translations, then the
figures that compare them.

The three steps run one after the other, all at the thread counts of --threads:
  1. Benchmarks/TLA/scripts/run_all.py runs TLC, into benchmark-results/<--tlc-name>.
  2. scripts/bench-model-check-all.py runs Veil, into benchmark-results/<--veil-name>.
  3. scripts/plot-model-check-runs-all.py draws benchmark-results/comparison_time.pdf and
     benchmark-results/comparison_memory.pdf, from all the results in both directories.

Each step skips the runs whose results it has recorded, so repeating the command continues an
interrupted evaluation:
  - TLC reuses a recorded result, unless the run was interrupted, a file it read has changed
    since, or it timed out with a shorter timeout (see run_tlc.py).
  - Veil resumes a run that has results (--resume of bench-model-check-all.py), and makes only
    the runs it is missing.
A new Veil run makes 3 runs per benchmark and thread count. A resumed one keeps its own number.
--repeat gives another in both cases. To start a step over, delete its directory.

A step that fails does not stop the next ones. The exit code is then 1. An interrupt (Ctrl-C)
stops the evaluation. Paths are relative to the root of the checkout.

Needs what the steps need: Java 11 or later and the packages in
Benchmarks/TLA/scripts/requirements.txt for TLC, Lean's `lake` on PATH for Veil, and matplotlib
and numpy for the figures. From anywhere:
  python3 scripts/tlc-vs-veil-mc-evaluation.py --threads 1-14       # into benchmark-results/tlc and benchmark-results/all
  python3 scripts/tlc-vs-veil-mc-evaluation.py --threads 8 14 --tlc-name tlc-8-14 --veil-name veil-8-14 --repeat 1
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shlex
import signal
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
# The scripts of the steps, relative to ROOT
TLC = "Benchmarks/TLA/scripts/run_all.py"
VEIL = "scripts/bench-model-check-all.py"
PLOT = "scripts/plot-model-check-runs-all.py"


def thread_counts(text: str) -> list:
    """The thread counts of one argument of --threads: N, N-M for N to M, or several of them
    separated by commas."""
    counts = []
    for part in text.split(","):
        match = re.fullmatch(r"([1-9][0-9]*)(?:-([1-9][0-9]*))?", part.strip())
        low, high = (int(match[1]), int(match[2] or match[1])) if match else (0, -1)
        if high < low:
            raise argparse.ArgumentTypeError(f"expected N or N-M with 0 < N <= M, got {part!r}")
        counts += range(low, high + 1)
    return counts


def directory_name(text: str) -> str:
    """A directory in benchmark-results, given by its name."""
    if text in ("", ".", "..") or "/" in text or os.sep in text:
        raise argparse.ArgumentTypeError(f"expected the name of a directory in benchmark-results, got {text!r}")
    return text


def run(command: list) -> int:
    """Run the script command[0] with this Python and the arguments command[1:]; return its exit
    code."""
    process = subprocess.Popen([sys.executable, *command])
    # An interrupt from the terminal also reaches the script, which stops its own processes and
    # exits: until then, wait for it.
    previous = signal.signal(signal.SIGINT, signal.SIG_IGN)
    try:
        code = process.wait()
    finally:
        signal.signal(signal.SIGINT, previous)
    # As a shell reports a command that a signal ended
    return 128 - code if code < 0 else code


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter,
                                 allow_abbrev=False)
    ap.add_argument("--threads", type=thread_counts, nargs="+", required=True, metavar="N[-M]",
                    help="thread counts, the workers of TLC and the threads of Veil: e.g. 8 14, 8,14 or 1-14 "
                         "(1 to 14); 1 is Veil's sequential search")
    ap.add_argument("--tlc-name", type=directory_name, default="tlc",
                    help="directory of the TLC results in benchmark-results (default tlc)")
    ap.add_argument("--veil-name", type=directory_name, default="all",
                    help="name of the Veil run, and of its directory in benchmark-results (default all)")
    ap.add_argument("-r", "--repeat", type=int,
                    help="runs per Veil benchmark and thread count (default 3 for a new Veil run, or the run's "
                         "own when it is resumed)")
    ap.add_argument("-o", "--output", default="benchmark-results/comparison",
                    help="prefix of the figures, PREFIX_time.pdf and PREFIX_memory.pdf (default "
                         "benchmark-results/comparison)")
    args = ap.parse_args()
    if args.repeat is not None and args.repeat < 1:
        ap.error("--repeat must be at least 1")
    threads = list(dict.fromkeys(t for counts in args.threads for t in counts))
    os.chdir(ROOT)
    tlc, veil = f"benchmark-results/{args.tlc_name}", f"benchmark-results/{args.veil_name}"
    steps = [
        ("TLC", [TLC, "--workers", *map(str, threads), "--output", tlc]),
        ("Veil", [VEIL, "--threads", ",".join(map(str, threads)), "--name", args.veil_name]
         + (["--repeat", str(args.repeat)] if args.repeat is not None else [])
         # bench-model-check-all.py refuses to start a run over the results of another
         + (["--resume"] if Path(veil, "results.json").exists() else [])),
        ("figures", [PLOT, tlc, veil, "-o", args.output]),
    ]
    failed = []
    for i, (name, command) in enumerate(steps, 1):
        print(("\n" if i > 1 else "") + f"== {i}/{len(steps)} {name}: {shlex.join(command)}", flush=True)
        code = run(command)
        if code == 128 + signal.SIGINT:
            print(f"{name}: interrupted; run the same command again to continue", file=sys.stderr)
            return code
        if code:
            failed.append(f"{name} (exit code {code})")
    if failed:
        print(f"\nfailed: {', '.join(failed)}; see above", file=sys.stderr)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
