#!/usr/bin/env python3
"""Count the lines of code of the TLA+ benchmarks and of their Veil models, as a Markdown table.

Run from any directory:
    python3 Benchmarks/TLA/scripts/loc_ratio_all.py > loc.md
    python3 Benchmarks/TLA/scripts/loc_ratio_all.py --pluscal source
    python3 Benchmarks/TLA/scripts/loc_ratio_all.py --json    # the same counts, for other scripts

Counts every pair in PAIRS below with loc_ratio.py, where the counting rules are defined, and
prints one row per pair: the lines of code of the TLA+ spec and of the Veil model, and their
ratio (Veil / TLA+). The specs of the pairs in BEFORE count only before the first line that
starts with the word given there (loc_ratio.py --before). The models that fetch_upstream.py
provides are downloaded first when they are missing; its messages go to stderr. Requires only
Python 3.9+. Exit 1 means a listed file is missing; the JSON gives null as its lines of code.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys

import fetch_upstream
import loc_ratio


HERE = Path(__file__).resolve().parent
BENCHMARKS = HERE.parent
REPO = HERE.parents[2]
EXAMPLES = REPO / "Examples"
# name, .tla file (in Benchmarks/TLA), Veil model (in Examples)
PAIRS = [
    ("Bakery", "TLAPlusExamples/Bakery.tla", "TLA/Bakery.lean"),
    ("Mutex", "MutexViolation.tla", "TLA/MutexViolation.lean"),
    ("Peterson", "TLAPlusExamples/Peterson.tla", "TLA/Peterson.lean"),
    ("FileLease", "FileBasedLease/FileBasedLease.tla", "TLA/FileBasedLease.lean"),
    ("TicketSem", "OrderedTicketSemaphore/OrderedTicketSemaphore.tla", "TLA/OrderedTicketSemaphore.lean"),
    ("KeyValueStore", "TLAPlusExamples/KeyValueStore.tla", "TLA/KeyValueStore.lean"),
    ("KVSnap", "TLAPlusExamples/KVSnap/KVsnap.tla", "TLA/KVSnap.lean"),
    ("German", "German.tla", "TLA/German.lean"),
    ("Cosmos", "CosmosDB/swscop.tla", "TLA/CosmosDB.lean"),
    ("LeaderlessLog", "LeaderlessLog/LeaderlessLog.tla", "TLA/LeaderlessLog.lean"),
    ("Oswald", "Oswald/Oswald.tla", "TLA/Oswald.lean"),
    ("Percolator", "Percolator/Percolator.tla", "TLA/Percolator.lean"),
    ("ParCommits", "ParallelCommits/ParallelCommits.tla", "TLA/ParallelCommits.lean"),
    ("RiverCrossing", "FarmerGooseFox.tla", "Puzzles/RiverCrossing.lean"),
    ("Prisoners", "TLAPlusExamples/Prisoners.tla", "Puzzles/Prisoners.lean"),
    ("Room", "Room.tla", "TLA/Room.lean"),
    ("DieHard", "TLAPlusExamples/DieHard.tla", "Puzzles/DieHard.lean"),
    ("AWSDNS", "AWS/AWS.tla", "TLA/AWSDnsRace.lean"),
    ("SimpAllocator", "TLAPlusExamples/SimpleAllocator.tla", "TLA/SimpleAllocator.lean"),
    ("2PC", "TLAPlusExamples/TwoPhaseCommit.tla", "TLA/TwoPhaseCommit.lean"),
    ("bcastByz", "TLAPlusExamples/bcastByz.tla", "TLA/BcastByz.lean"),
    ("EWD840", "TLAPlusExamples/EWD840.tla", "TLA/EWD840.lean"),
    ("Paxos", "Paxos/Paxos.tla", "TLA/Paxos.lean"),
    ("MultiPaxos", "MultiPaxosUs.tla", "TLA/MultiPaxos.lean"),
    ("NOPaxos", "NOPaxos/NOPaxos.tla", "TLA/NOPaxos.lean"),
    ("PAStatic", "ProposerAcceptorStatic/ProposerAcceptorStatic.tla", "TLA/ProposerAcceptorStatic.lean"),
    ("LeaseGuard", "LeaseGuard/leaseGuard.tla", "TLA/LeaseGuard.lean"),
    ("TaskClaiming", "TaskClaiming/TaskClaiming.tla", "TLA/TaskClaiming.lean"),
]
# MultiPaxosUs.tla has TLAPS lemmas and their proofs from its first LEMMA on
BEFORE = {"MultiPaxos": "LEMMA"}


def count_pairs(pluscal):
    """Every pair of PAIRS with the lines of code of its files (None for a missing file)."""
    pinned = {BENCHMARKS / name for name, *_ in fetch_upstream.FILES}
    if any(BENCHMARKS / tla in pinned and not (BENCHMARKS / tla).is_file() for _, tla, _ in PAIRS):
        # Its messages go to stderr, so that stdout has only the counts
        subprocess.run([sys.executable, str(HERE / "fetch_upstream.py")], stdout=sys.stderr)
    rows = []
    for name, tla, veil in PAIRS:
        spec, model = BENCHMARKS / tla, EXAMPLES / veil
        tla_loc = loc_ratio.count_tla(spec, pluscal, BEFORE.get(name)).loc if spec.is_file() else None
        veil_loc = loc_ratio.count_lean(model) if model.is_file() else None
        rows.append({"name": name, "tla": str(spec.relative_to(REPO)), "tla_before": BEFORE.get(name),
                     "tla_loc": tla_loc, "veil": str(model.relative_to(REPO)), "veil_loc": veil_loc,
                     "ratio": None if None in (tla_loc, veil_loc) else loc_ratio.ratio(tla_loc, veil_loc)})
    return rows


def markdown(rows, pluscal):
    lines = ["| Benchmark | TLA+ spec | TLA+ LOC | Veil model | Veil LOC | Ratio |",
             "|---|---|--:|---|--:|--:|"]
    for row in rows:
        loc = ["missing" if row[key] is None else str(row[key]) for key in ("tla_loc", "veil_loc")]
        lines.append(f"| {row['name']} | `{row['tla']}` | {loc[0]} | `{row['veil']}` | {loc[1]} "
                     f"| {row['ratio'] or '--'} |")
    notes = [f"Counted by `loc_ratio.py` with `--pluscal {pluscal}`"]
    notes += [f"{name} with `--before {word}`" for name, word in BEFORE.items()]
    return "\n".join(lines) + "\n\n" + "; ".join(notes) + "."


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--pluscal", choices=loc_ratio.PLUSCAL_MODES, default="both",
                        help="what a PlusCal spec contributes (default: both; see loc_ratio.py)")
    parser.add_argument("--json", action="store_true", help="print the counts as JSON instead of a table")
    args = parser.parse_args()
    rows = count_pairs(args.pluscal)
    if args.json:
        print(json.dumps({"pluscal_mode": args.pluscal, "pairs": rows}, indent=2))
    else:
        print(markdown(rows, args.pluscal))
    missing = [row[side] for row in rows for side in ("tla", "veil") if row[f"{side}_loc"] is None]
    for path in missing:
        print(f"Missing: {path}", file=sys.stderr)
    return 1 if missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
