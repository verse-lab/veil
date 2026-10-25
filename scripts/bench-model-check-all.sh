#!/bin/bash
#
# Benchmark the compiled model checkers of the standard benchmark set, Benchmarks/Veil/Standard:
# an example of running scripts/bench-model-check.py. Every spec of the set is elaborated and
# compiled once (compilation timed), then its checker binary is run REPEAT times at each thread
# count; scripts/bench-model-check-report.py prints the tables (medians) and writes the CSVs.
#
# Usage, from anywhere, after `lake build` in the checkout:
#   ./scripts/bench-model-check-standard.sh                          # the run "standard", in benchmark-results/standard
#   NAME=standard-12threads THREADS=12 ./scripts/bench-model-check-standard.sh
#   THREADS=1,4,8 REPEAT=5 BIN_DIR=benchmark-results/standard/bin ./scripts/bench-model-check-standard.sh
#   ./scripts/bench-model-check-standard.sh --only Mutex EWD840     # extra arguments go to bench-model-check.py
#   ./scripts/bench-model-check-standard.sh --dry-run               # only list the specs
#   BIN_DIR=benchmark-results/standard/bin ./scripts/bench-model-check-standard.sh --clean-binaries
#                                                                   # delete the kept binaries, after confirmation
#
# Settings (environment variables):
#   NAME         name of the run; all its output goes to benchmark-results/<NAME> (default standard)
#   OUT          output directory, overriding the one derived from NAME
#   THREADS      thread counts, comma-separated; 1 is the sequential search (default 1,4,8)
#   THRESHOLD    thresholdToParallel of the parallel search (default 20)
#   REPEAT       runs per spec and thread count; the report takes the median (default 3)
#   RUN_TIMEOUT  seconds per run, 0 for none (default 3600)
#   BIN_DIR      keep a copy of every binary there (default: binaries are not kept)
#
# A full pass over the set takes hours. The console output is also saved as console.log in the
# output directory. A run that was interrupted is continued with `--resume` (same NAME); to start
# it over, delete its directory first.
# To print the tables again later: python3 scripts/bench-model-check-report.py benchmark-results/<NAME>

set -euo pipefail
cd "$(dirname "$0")/.."    # bench-model-check.py runs from the root of the checkout

NAME="${NAME:-standard}"
OUT="${OUT:-benchmark-results/$NAME}"
THREADS="${THREADS:-1,4,8}"
THRESHOLD="${THRESHOLD:-20}"
REPEAT="${REPEAT:-3}"
RUN_TIMEOUT="${RUN_TIMEOUT:-3600}"

args=(Benchmarks/Veil/Standard
      --threads "$THREADS" --threshold "$THRESHOLD" --repeat "$REPEAT" --run-timeout "$RUN_TIMEOUT"
      --name "$NAME" --out "$OUT")
if [[ -n "${BIN_DIR:-}" ]]; then
    args+=(--bin-dir "$BIN_DIR")
fi

# On macOS, keep the machine from idle-sleeping during the run (this does not change CPU clocks).
runner=()
if command -v caffeinate > /dev/null 2>&1; then
    runner=(caffeinate -i)
fi

if [[ " $* " == *" --dry-run "* ]]; then
    exec python3 scripts/bench-model-check.py "${args[@]}" "$@"
fi
if [[ " $* " == *" --clean-binaries "* ]]; then
    bin_args=()
    if [[ -n "${BIN_DIR:-}" ]]; then
        bin_args=(--bin-dir "$BIN_DIR")
    fi
    exec python3 scripts/bench-model-check.py "${bin_args[@]}" "$@"
fi

mkdir -p "$OUT"
echo "run $NAME: threads $THREADS, thresholdToParallel $THRESHOLD, $REPEAT run(s) per spec and thread count, timeout ${RUN_TIMEOUT}s per run"
echo "output: $OUT"
"${runner[@]}" python3 scripts/bench-model-check.py "${args[@]}" "$@" 2>&1 | tee -a "$OUT/console.log"
