#!/bin/bash
#
# Profile a single Lean file
#
# Usage: ./scripts/profile-file.sh <file.lean> [output.json] [parse-profile.py options...]
#
# Examples:
#   ./scripts/profile-file.sh Examples/Tutorial/RingDec.lean
#   ./scripts/profile-file.sh Test/Ring.lean ring-profile.json
#   ./scripts/profile-file.sh Examples/Ivy/Ring.lean --exclude veil.perf.discharger
#   ./scripts/profile-file.sh Examples/Ivy/Ring.lean ring.json --filter veil.perf.tactic
#
# Output:
#   - JSON profile viewable at profiler.firefox.com
#   - Timing summary from parse-profile.py

set -e

FILE="$1"
shift || true

# If second arg doesn't start with -, treat it as output filename
if [[ -n "$1" && ! "$1" =~ ^- ]]; then
    OUTPUT="$1"
    shift
else
    OUTPUT="$(basename "$FILE" .lean).json"
fi

# Remaining args are passed to parse-profile.py
PARSE_ARGS=("$@")

if [[ -z "$FILE" ]]; then
    echo "Usage: $0 <file.lean> [output.json] [parse-profile.py options...]"
    echo ""
    echo "Examples:"
    echo "  $0 Examples/Ring.lean"
    echo "  $0 Examples/Ring.lean --exclude veil.perf.discharger"
    echo "  $0 Examples/Ring.lean ring.json --filter veil.perf.tactic"
    exit 1
fi

if [[ ! -f "$FILE" ]]; then
    echo "Error: '$FILE' not found"
    exit 1
fi

echo "Profiling: $FILE"
echo "Output: $OUTPUT"
echo ""

CMD="lake lean \"$FILE\" -- -Dtrace.profiler=true -Dtrace.profiler.output=\"$OUTPUT\" -Dtrace.veil.perf=true"
echo "Running: $CMD"
echo ""

START_TIME=$(date +%s.%N)

lake lean "$FILE" -- \
    -Dtrace.profiler=true \
    -Dtrace.profiler.output="$OUTPUT" \
    -Dtrace.veil.perf=true

END_TIME=$(date +%s.%N)
ELAPSED=$(echo "$END_TIME - $START_TIME" | bc)

echo ""
echo "Completed in ${ELAPSED}s"
echo ""
echo "Profile saved to: $OUTPUT"
echo "View at: https://profiler.firefox.com/"
echo ""

# Run parse-profile.py to show results
SCRIPT_DIR="$(dirname "$0")"
if [[ -f "$SCRIPT_DIR/parse-profile.py" ]]; then
    "$SCRIPT_DIR/parse-profile.py" "$OUTPUT" "${PARSE_ARGS[@]}"
fi
