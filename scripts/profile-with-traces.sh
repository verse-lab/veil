#!/bin/bash
#
# Profile Lean files with Veil-specific traces enabled
#
# Usage: ./scripts/profile-with-traces.sh <file.lean> [output.json]
#
# This script enables veil.perf traces in addition to the profiler,
# giving more detailed breakdown of Veil operations.
#
# Examples:
#   ./scripts/profile-with-traces.sh Examples/Tutorial/RingDec.lean
#   ./scripts/profile-with-traces.sh Test/Ring.lean ring-profile.json

set -e

FILE="$1"
OUTPUT="${2:-$(basename "$FILE" .lean).json}"
LOG="${OUTPUT%.json}.log"

if [[ -z "$FILE" ]]; then
    echo "Usage: $0 <file.lean> [output.json]"
    exit 1
fi

if [[ ! -f "$FILE" ]]; then
    echo "Error: '$FILE' not found"
    exit 1
fi

echo "Profiling with Veil traces: $FILE"
echo "Output: $OUTPUT"
echo "Log: $LOG"
echo ""

START_TIME=$(date +%s.%N)

# Run with both profiler and Veil traces
lake lean "$FILE" -- \
    -Dtrace.profiler=true \
    -Dtrace.profiler.output="$OUTPUT" \
    -Dtrace.veil.perf=true \
    2>&1 | tee "$LOG"

END_TIME=$(date +%s.%N)
ELAPSED=$(echo "$END_TIME - $START_TIME" | bc)

echo ""
echo "Completed in ${ELAPSED}s"
echo ""
echo "Profile saved to: $OUTPUT"
echo "Trace log saved to: $LOG"
echo ""
echo "View profile at: https://profiler.firefox.com/"
echo ""
echo "Veil trace summary (from log):"
echo "------------------------------"
# Extract Veil perf traces from log if any
grep -E "^\[veil\.perf" "$LOG" 2>/dev/null || echo "(no veil.perf traces in output)"
