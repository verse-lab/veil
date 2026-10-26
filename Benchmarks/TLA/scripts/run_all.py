#!/usr/bin/env python3
"""Run TLC on all the TLA+ benchmarks, with 1 to as many workers as this machine has CPUs.

First downloads, with fetch_upstream.py, the models that the repository does not include and
that are not there yet. Then runs run_tlc.py on the benchmarks below, the .tla and .cfg files in
Benchmarks/TLA, each with every worker count; --workers gives other counts, and the other
arguments go to run_tlc.py (see its --help), e.g. --dry-run, --heap or --output. As run_tlc.py
skips the runs whose results it has recorded, repeating the command resumes an interrupted run.
On macOS, the machine is kept from idle-sleeping meanwhile.

From the repository root, with Java 11 or later and the packages in requirements.txt:
  python3 Benchmarks/TLA/scripts/run_all.py              # into benchmark-results/tlc
  python3 Benchmarks/TLA/scripts/run_all.py --dry-run    # only list the runs
  python3 Benchmarks/TLA/scripts/run_all.py --workers 1 4 8 --heap 8G
"""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
BENCHMARKS = HERE.parent
# name, .tla file, .cfg file (in Benchmarks/TLA)
PAIRS = [
    ("Bakery", "TLAPlusExamples/Bakery.tla", "TLAPlusExamples/Bakery.cfg"),
    ("EWD840", "TLAPlusExamples/EWD840.tla", "TLAPlusExamples/EWD840.cfg"),
    ("German", "German.tla", "German.cfg"),
    ("KeyValueStore", "TLAPlusExamples/KeyValueStore.tla", "TLAPlusExamples/KeyValueStore.cfg"),
    ("MultiPaxos", "MCMultiPaxosUs.tla", "MultiPaxosUs.cfg"),
    ("Mutex", "MutexViolation.tla", "MutexViolation.cfg"),
    ("NOPaxos", "NOPaxos/MCNOPaxos.tla", "NOPaxos/NOPaxos.cfg"),
    ("Paxos", "Paxos/Paxos.tla", "Paxos/Paxos.cfg"),
    ("SimpAllocator", "TLAPlusExamples/SimpleAllocator.tla", "TLAPlusExamples/SimpleAllocator.cfg"),
    ("2PC", "TLAPlusExamples/TwoPhaseCommit.tla", "TLAPlusExamples/TwoPhaseCommit.cfg"),
    ("bcastByz", "TLAPlusExamples/bcastByz.tla", "TLAPlusExamples/bcastByz.cfg"),
    ("FileLease", "FileBasedLease/FileBasedLease.tla", "FileBasedLease/FileBasedLease.cfg"),
    ("LeaderlessLog", "LeaderlessLog/LeaderlessLog.tla", "LeaderlessLog/LeaderlessLog.cfg"),
    ("LeaseGuard", "LeaseGuard/mcLeaseGuard.tla", "LeaseGuard/LeaseGuard.cfg"),
    ("TicketSem", "OrderedTicketSemaphore/MCOrderedTicketSemaphore.tla",
     "OrderedTicketSemaphore/OrderedTicketSemaphore.cfg"),
    ("Oswald", "Oswald/Oswald.tla", "Oswald/Oswald.cfg"),
    ("ParCommits", "ParallelCommits/ParallelCommits.tla", "ParallelCommits/ParallelCommits.cfg"),
    ("Percolator", "Percolator/Percolator.tla", "Percolator/Percolator.cfg"),
    ("PAStatic", "ProposerAcceptorStatic/MCProposerAcceptorStatic.tla",
     "ProposerAcceptorStatic/ProposerAcceptorStatic.cfg"),
    ("TaskClaiming", "TaskClaiming/TaskClaiming.tla", "TaskClaiming/TaskClaiming.cfg"),
]


def cpu_count():
    """The CPUs this process may run on (all of them, unless its affinity is restricted)."""
    return len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else os.cpu_count()


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--workers", type=int, nargs="+", default=list(range(1, cpu_count() + 1)),
                        help=f"TLC worker counts (default: 1 to {cpu_count()}, the CPUs of this machine)")
    args, rest = parser.parse_known_args()
    fetch = subprocess.run([sys.executable, str(HERE / "fetch_upstream.py")])
    if fetch.returncode:
        print("fetch_upstream.py could not provide the models it downloads; see above.", file=sys.stderr)
        return fetch.returncode
    command = [sys.executable, str(HERE / "run_tlc.py"), "--workers", *map(str, args.workers)]
    for name, spec, cfg in PAIRS:
        command += ["--pair", str(BENCHMARKS / spec), str(BENCHMARKS / cfg), name]
    if shutil.which("caffeinate"):
        # Until this process, which becomes run_tlc.py, exits
        subprocess.Popen(["caffeinate", "-i", "-w", str(os.getpid())])
    os.execv(sys.executable, command + rest)


if __name__ == "__main__":
    sys.exit(main())
