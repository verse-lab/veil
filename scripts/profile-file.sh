#!/bin/bash
#
# Profile a single Lean file
#
# Usage: ./scripts/profile-file.sh <file.lean> [output.json]
#
# Examples:
#   ./scripts/profile-file.sh Examples/Tutorial/RingDec.lean
#   ./scripts/profile-file.sh Test/Ring.lean ring-profile.json
#
# Output:
#   - JSON profile viewable at profiler.firefox.com

set -e

FILE="$1"
OUTPUT="${2:-$(basename "$FILE" .lean).json}"

if [[ -z "$FILE" ]]; then
    echo "Usage: $0 <file.lean> [output.json]"
    exit 1
fi

if [[ ! -f "$FILE" ]]; then
    echo "Error: '$FILE' not found"
    exit 1
fi

echo "Profiling: $FILE"
echo "Output: $OUTPUT"
echo ""

CMD="lake lean \"$FILE\" -- -Dtrace.profiler=true -Dtrace.profiler.output=\"$OUTPUT\""
echo "Running: $CMD"
echo ""

START_TIME=$(date +%s.%N)

lake lean "$FILE" -- \
    -Dtrace.profiler=true \
    -Dtrace.profiler.output="$OUTPUT"

END_TIME=$(date +%s.%N)
ELAPSED=$(echo "$END_TIME - $START_TIME" | bc)

echo ""
echo "Completed in ${ELAPSED}s"
echo ""
echo "Profile saved to: $OUTPUT"
echo "View at: https://profiler.firefox.com/"
