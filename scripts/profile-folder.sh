#!/bin/bash
#
# Profile all Lean files in a folder and collate results
#
# Usage: ./scripts/profile-folder.sh <folder> [output-dir]
#
# Examples:
#   ./scripts/profile-folder.sh Examples/Tutorial
#   ./scripts/profile-folder.sh Test profiles/test-run
#
# Output:
#   - Individual .json profiles for each file (viewable at profiler.firefox.com)
#   - summary.txt with timing information for all files
#   - summary.csv for spreadsheet analysis

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Parse arguments
FOLDER="${1:-.}"
OUTPUT_DIR="${2:-profiles/$(date +%Y%m%d-%H%M%S)}"

if [[ ! -d "$FOLDER" ]]; then
    echo -e "${RED}Error: '$FOLDER' is not a directory${NC}"
    echo "Usage: $0 <folder> [output-dir]"
    exit 1
fi

# Create output directory
mkdir -p "$OUTPUT_DIR"

echo -e "${GREEN}Profiling Lean files in: $FOLDER${NC}"
echo -e "${GREEN}Output directory: $OUTPUT_DIR${NC}"
echo ""

# Find all .lean files
LEAN_FILES=$(find "$FOLDER" -name "*.lean" -type f | sort)
FILE_COUNT=$(echo "$LEAN_FILES" | wc -l | tr -d ' ')

if [[ -z "$LEAN_FILES" ]]; then
    echo -e "${RED}No .lean files found in $FOLDER${NC}"
    exit 1
fi

echo "Found $FILE_COUNT Lean files to profile"
echo ""

# Initialize summary files
SUMMARY_FILE="$OUTPUT_DIR/summary.txt"
CSV_FILE="$OUTPUT_DIR/summary.csv"

echo "Veil Profiling Summary" > "$SUMMARY_FILE"
echo "======================" >> "$SUMMARY_FILE"
echo "Date: $(date)" >> "$SUMMARY_FILE"
echo "Folder: $FOLDER" >> "$SUMMARY_FILE"
echo "" >> "$SUMMARY_FILE"

echo "file,status,time_seconds,profile_file" > "$CSV_FILE"

# Track statistics
TOTAL_TIME=0
SUCCESS_COUNT=0
FAIL_COUNT=0

# Process each file
for FILE in $LEAN_FILES; do
    BASENAME=$(basename "$FILE" .lean)
    RELATIVE_PATH="${FILE#$FOLDER/}"
    PROFILE_NAME="${RELATIVE_PATH//\//_}"
    PROFILE_NAME="${PROFILE_NAME%.lean}.json"
    PROFILE_PATH="$OUTPUT_DIR/$PROFILE_NAME"

    echo -n "Profiling $RELATIVE_PATH... "

    START_TIME=$(date +%s.%N)

    # Run with profiler
    if lake lean "$FILE" -- \
        -Dtrace.profiler=true \
        -Dtrace.profiler.output="$PROFILE_PATH" \
        > "$OUTPUT_DIR/${PROFILE_NAME%.json}.log" 2>&1; then

        END_TIME=$(date +%s.%N)
        ELAPSED=$(echo "$END_TIME - $START_TIME" | bc)
        TOTAL_TIME=$(echo "$TOTAL_TIME + $ELAPSED" | bc)
        SUCCESS_COUNT=$((SUCCESS_COUNT + 1))

        echo -e "${GREEN}OK${NC} (${ELAPSED}s)"
        echo "$RELATIVE_PATH: ${ELAPSED}s - OK" >> "$SUMMARY_FILE"
        echo "$RELATIVE_PATH,ok,$ELAPSED,$PROFILE_NAME" >> "$CSV_FILE"
    else
        END_TIME=$(date +%s.%N)
        ELAPSED=$(echo "$END_TIME - $START_TIME" | bc)
        FAIL_COUNT=$((FAIL_COUNT + 1))

        echo -e "${RED}FAILED${NC} (${ELAPSED}s)"
        echo "$RELATIVE_PATH: ${ELAPSED}s - FAILED" >> "$SUMMARY_FILE"
        echo "$RELATIVE_PATH,failed,$ELAPSED," >> "$CSV_FILE"
    fi
done

# Write summary statistics
echo "" >> "$SUMMARY_FILE"
echo "Statistics" >> "$SUMMARY_FILE"
echo "----------" >> "$SUMMARY_FILE"
echo "Total files: $FILE_COUNT" >> "$SUMMARY_FILE"
echo "Successful: $SUCCESS_COUNT" >> "$SUMMARY_FILE"
echo "Failed: $FAIL_COUNT" >> "$SUMMARY_FILE"
echo "Total time: ${TOTAL_TIME}s" >> "$SUMMARY_FILE"

echo ""
echo -e "${GREEN}Profiling complete!${NC}"
echo ""
echo "Results:"
echo "  - Profiles: $OUTPUT_DIR/*.json"
echo "  - Summary:  $SUMMARY_FILE"
echo "  - CSV:      $CSV_FILE"
echo ""
echo "Statistics:"
echo "  - Total files: $FILE_COUNT"
echo "  - Successful: $SUCCESS_COUNT"
echo "  - Failed: $FAIL_COUNT"
echo "  - Total time: ${TOTAL_TIME}s"
echo ""
echo "To view a profile, upload the .json file to:"
echo "  https://profiler.firefox.com/"
