#!/bin/bash
#
# Profile a single Lean file
#
# Usage: ./scripts/profile-file.sh [options] <file.lean> [output.json] [parse-profile.py options...]
#
# Options:
#   --quiet, -q    Skip running parse-profile.py (just generate the JSON)
#
# Examples:
#   ./scripts/profile-file.sh Examples/Tutorial/RingDec.lean
#   ./scripts/profile-file.sh Test/Ring.lean ring-profile.json
#   ./scripts/profile-file.sh Examples/Ivy/Ring.lean --exclude veil.perf.discharger
#   ./scripts/profile-file.sh Examples/Ivy/Ring.lean ring.json --filter veil.perf.tactic
#   ./scripts/profile-file.sh --quiet Examples/Ivy/Ring.lean  # JSON only, no summary
#
# Output:
#   - JSON profile viewable at profiler.firefox.com
#   - Timing summary from parse-profile.py (unless --quiet)

set -e

# Parse our own options first
QUIET=false
while [[ "$1" =~ ^- ]]; do
    case "$1" in
        --quiet|-q)
            QUIET=true
            shift
            ;;
        *)
            break
            ;;
    esac
done

FILE="$1"
shift || true

# If next arg doesn't start with -, treat it as output filename
if [[ -n "$1" && ! "$1" =~ ^- ]]; then
    OUTPUT="$1"
    shift
else
    OUTPUT="$(basename "$FILE" .lean).json"
fi

# Remaining args are passed to parse-profile.py
PARSE_ARGS=("$@")

if [[ -z "$FILE" ]]; then
    echo "Usage: $0 [--quiet] <file.lean> [output.json] [parse-profile.py options...]"
    echo ""
    echo "Options:"
    echo "  --quiet, -q    Skip running parse-profile.py (just generate the JSON)"
    echo ""
    echo "Examples:"
    echo "  $0 Examples/Ring.lean"
    echo "  $0 Examples/Ring.lean --exclude veil.perf.discharger"
    echo "  $0 Examples/Ring.lean ring.json --filter veil.perf.tactic"
    echo "  $0 --quiet Examples/Ring.lean  # JSON only"
    exit 1
fi

if [[ ! -f "$FILE" ]]; then
    echo "Error: '$FILE' not found"
    exit 1
fi

echo "Profiling: $FILE"
echo "Output: $OUTPUT"
echo ""

CMD="lake lean \"$FILE\" -- -Dtrace.profiler=true -Dtrace.profiler.output=\"$OUTPUT\" -Dtrace.veil.perf=true -Dtrace.smt.perf=true"
echo "Running: $CMD"
echo ""

START_TIME=$(date +%s.%N)

lake lean "$FILE" -- \
    -Dtrace.profiler=true \
    -Dtrace.profiler.output="$OUTPUT" \
    -Dtrace.veil.perf=true \
    -Dtrace.smt.perf=true

END_TIME=$(date +%s.%N)
REAL_TIME=$(echo "scale=2; ($END_TIME - $START_TIME) / 1" | bc)

SCRIPT_DIR="$(dirname "$0")"

# Get CPU time from profile
CPU_TIME_MS=0
if [[ -f "$SCRIPT_DIR/parse-profile.py" && -f "$OUTPUT" ]]; then
    CPU_TIME_MS=$("$SCRIPT_DIR/parse-profile.py" "$OUTPUT" --total-only --all 2>/dev/null || echo "0")
fi
CPU_TIME=$(echo "scale=2; $CPU_TIME_MS / 1000" | bc)

echo ""
echo "Completed: real ${REAL_TIME}s / cpu ${CPU_TIME}s"
echo ""
echo "Profile saved to: $OUTPUT"
echo "View at: https://profiler.firefox.com/"
echo ""

# Run parse-profile.py to show results (unless --quiet)
if [[ "$QUIET" != "true" ]]; then
    if [[ -f "$SCRIPT_DIR/parse-profile.py" ]]; then
        "$SCRIPT_DIR/parse-profile.py" "$OUTPUT" "${PARSE_ARGS[@]}"
    fi
fi
