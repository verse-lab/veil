#!/bin/bash
#
# Profile all Lean files in a folder and collate results
#
# Usage: ./scripts/profile-folder.sh <folder> [output-dir] [parse-profile.py options...]
#
# Examples:
#   ./scripts/profile-folder.sh Examples/Tutorial
#   ./scripts/profile-folder.sh Test profiles/test-run
#   ./scripts/profile-folder.sh Examples --exclude veil.perf.discharger
#
# Output:
#   - Individual .json profiles for each file (viewable at profiler.firefox.com)
#   - summary.txt with timing information for all files
#   - summary.csv for spreadsheet analysis
#   - Aggregated timing summary from parse-profile.py

set -e

SCRIPT_DIR="$(dirname "$0")"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Function to show aggregated results (called on normal exit or interrupt)
show_aggregated_results() {
    local exit_reason="$1"

    if [[ ${#PROFILE_FILES[@]} -gt 0 ]]; then
        TIMING_FILE="$OUTPUT_DIR/timing.txt"
        echo ""
        if [[ "$exit_reason" == "interrupt" ]]; then
            echo -e "${YELLOW}Interrupted! Showing partial results (${#PROFILE_FILES[@]} profiles):${NC}"
        else
            echo -e "${GREEN}Aggregated timing summary:${NC}"
        fi
        # Write header with options used
        {
            echo "# Generated: $(date)"
            echo "# Options: ${PARSE_ARGS[*]:-<default>}"
            echo "# Profiles: ${#PROFILE_FILES[@]}"
            echo "#"
            echo "# To regenerate with different options:"
            echo "#   ./scripts/parse-profile.py \$(cat $OUTPUT_DIR/profiles.txt) [options]"
            echo ""
        } > "$TIMING_FILE"
        "$SCRIPT_DIR/parse-profile.py" "${PROFILE_FILES[@]}" "${PARSE_ARGS[@]}" | tee -a "$TIMING_FILE"
        echo ""
        echo "Timing saved to: $TIMING_FILE"
    else
        echo ""
        echo -e "${YELLOW}No profiles collected yet.${NC}"
    fi
}

# Trap Ctrl-C (SIGINT) to show partial results
trap 'echo ""; echo -e "${YELLOW}Caught interrupt signal...${NC}"; show_aggregated_results "interrupt"; exit 130' INT

# Parse arguments
FOLDER="${1:-.}"
shift || true

# If next arg doesn't start with -, treat it as output directory
if [[ -n "$1" && ! "$1" =~ ^- ]]; then
    OUTPUT_DIR="$1"
    shift
else
    OUTPUT_DIR="profiles/$(date +%Y%m%d-%H%M%S)"
fi

# Remaining args are passed to parse-profile.py
PARSE_ARGS=("$@")

if [[ ! -d "$FOLDER" ]]; then
    echo -e "${RED}Error: '$FOLDER' is not a directory${NC}"
    echo "Usage: $0 <folder> [output-dir] [parse-profile.py options...]"
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
PROFILES_FILE="$OUTPUT_DIR/profiles.txt"

echo "Veil Profiling Summary" > "$SUMMARY_FILE"
echo "======================" >> "$SUMMARY_FILE"
echo "Date: $(date)" >> "$SUMMARY_FILE"
echo "Folder: $FOLDER" >> "$SUMMARY_FILE"
echo "" >> "$SUMMARY_FILE"

echo "file,status,real_seconds,cpu_seconds,profile_file" > "$CSV_FILE"

# Clear profiles list (will be populated as we go)
: > "$PROFILES_FILE"

# Track statistics
TOTAL_REAL_TIME=0
TOTAL_CPU_TIME=0
SUCCESS_COUNT=0
FAIL_COUNT=0
PROFILE_FILES=()

# Process each file
for FILE in $LEAN_FILES; do
    RELATIVE_PATH="${FILE#$FOLDER/}"
    PROFILE_NAME="${RELATIVE_PATH//\//_}"
    PROFILE_NAME="${PROFILE_NAME%.lean}.json"
    PROFILE_PATH="$OUTPUT_DIR/$PROFILE_NAME"
    LOG_PATH="$OUTPUT_DIR/${PROFILE_NAME%.json}.log"

    echo -n "Profiling $RELATIVE_PATH... "

    START_TIME=$(date +%s.%N)

    # Use profile-file.sh with --quiet to skip individual parse output
    if "$SCRIPT_DIR/profile-file.sh" --quiet "$FILE" "$PROFILE_PATH" > "$LOG_PATH" 2>&1; then
        END_TIME=$(date +%s.%N)
        REAL_TIME=$(echo "scale=2; ($END_TIME - $START_TIME) / 1" | bc)
        TOTAL_REAL_TIME=$(echo "$TOTAL_REAL_TIME + $REAL_TIME" | bc)

        # Get CPU time from profile
        CPU_TIME_MS=$("$SCRIPT_DIR/parse-profile.py" "$PROFILE_PATH" --total-only --all 2>/dev/null || echo "0")
        CPU_TIME=$(echo "scale=2; $CPU_TIME_MS / 1000" | bc)
        TOTAL_CPU_TIME=$(echo "$TOTAL_CPU_TIME + $CPU_TIME" | bc)

        SUCCESS_COUNT=$((SUCCESS_COUNT + 1))
        PROFILE_FILES+=("$PROFILE_PATH")
        echo "$PROFILE_PATH" >> "$PROFILES_FILE"

        echo -e "${GREEN}OK${NC} (real ${REAL_TIME}s / cpu ${CPU_TIME}s)"
        echo "$RELATIVE_PATH: real ${REAL_TIME}s / cpu ${CPU_TIME}s - OK" >> "$SUMMARY_FILE"
        echo "$RELATIVE_PATH,ok,$REAL_TIME,$CPU_TIME,$PROFILE_NAME" >> "$CSV_FILE"
    else
        END_TIME=$(date +%s.%N)
        REAL_TIME=$(echo "scale=2; ($END_TIME - $START_TIME) / 1" | bc)
        FAIL_COUNT=$((FAIL_COUNT + 1))

        echo -e "${RED}FAILED${NC} (real ${REAL_TIME}s)"
        echo "$RELATIVE_PATH: real ${REAL_TIME}s - FAILED" >> "$SUMMARY_FILE"
        echo "$RELATIVE_PATH,failed,$REAL_TIME,,$PROFILE_NAME" >> "$CSV_FILE"
    fi
done

# Write summary statistics
echo "" >> "$SUMMARY_FILE"
echo "Statistics" >> "$SUMMARY_FILE"
echo "----------" >> "$SUMMARY_FILE"
echo "Total files: $FILE_COUNT" >> "$SUMMARY_FILE"
echo "Successful: $SUCCESS_COUNT" >> "$SUMMARY_FILE"
echo "Failed: $FAIL_COUNT" >> "$SUMMARY_FILE"
echo "Total time: real ${TOTAL_REAL_TIME}s / cpu ${TOTAL_CPU_TIME}s" >> "$SUMMARY_FILE"

echo ""
echo -e "${GREEN}Profiling complete!${NC}"
echo ""
echo "Results:"
echo "  - Profiles:      $OUTPUT_DIR/*.json"
echo "  - Profiles list: $PROFILES_FILE"
echo "  - Summary:       $SUMMARY_FILE"
echo "  - CSV:           $CSV_FILE"
echo ""
echo "Statistics:"
echo "  - Total files: $FILE_COUNT"
echo "  - Successful: $SUCCESS_COUNT"
echo "  - Failed: $FAIL_COUNT"
echo "  - Total time: real ${TOTAL_REAL_TIME}s / cpu ${TOTAL_CPU_TIME}s"
echo ""
echo "To view a profile, upload the .json file to:"
echo "  https://profiler.firefox.com/"
echo ""
echo "To re-analyze with different options:"
echo "  ./scripts/parse-profile.py \$(cat $PROFILES_FILE) [options]"
echo ""
echo "Examples:"
echo "  ./scripts/parse-profile.py \$(cat $PROFILES_FILE) -f veil.perf.elaborator"
echo "  ./scripts/parse-profile.py \$(cat $PROFILES_FILE) -f veil.perf.tactic -f veil.perf.extract"
echo "  ./scripts/parse-profile.py \$(cat $PROFILES_FILE) --exclude veil.perf.discharger"

# Aggregate results from all successful profiles
show_aggregated_results "complete"
