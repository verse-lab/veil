#!/usr/bin/env python3
"""
Build Paxos proof theorem files and report success/failure.

Usage:
    python scripts/build-paxos-proofs.py              # Build all theorem files (in parallel)
    python scripts/build-paxos-proofs.py <file.lean>  # Build a single file
"""

import subprocess
import sys
import os
import re
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

PROOFS_DIR = Path("Examples/Paxos/PaxosProof")
EXCLUDED_FILES = {"Spec.lean"}  # Files to skip when building all
MAX_WORKERS = os.cpu_count() or 4  # Use all available CPUs
LEAN_INCOMPLETE_TERM = "s" + "orry"

# Known actions and invariants for the summary table
ACTIONS = ["initializer", "Phase1a", "Phase1b", "Phase2a", "Phase2b"]
INVARIANTS = [
    "doesNotThrow", "Consistency", "TypeOK", "MsgInv1b", "MsgInv2a",
    "MsgInv2b", "AccInv", "two_a_valid_ballot", "VotedInv", "VotedOnce"
]


def find_project_root() -> Path:
    """Find the project root by looking for lakefile.lean"""
    current = Path(__file__).resolve().parent
    while current != current.parent:
        if (current / "lakefile.lean").exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root (no lakefile.lean found)")


def check_for_sorry(filepath: Path) -> list[tuple[int, str]]:
    """
    Check whether a file contains Lean incomplete-proof markers.
    Returns a list of (line_number, line_content) for matching lines.
    Ignores matches in comments.
    """
    sorry_lines = []
    try:
        with open(filepath, "r") as f:
            in_block_comment = False
            for i, line in enumerate(f, 1):
                # Track block comments
                if "/-" in line:
                    in_block_comment = True
                if "-/" in line:
                    in_block_comment = False
                    continue
                if in_block_comment:
                    continue
                # Skip line comments
                code_part = line.split("--")[0]
                # Check as a word boundary, not as part of another identifier.
                if re.search(rf'\b{LEAN_INCOMPLETE_TERM}\b', code_part):
                    sorry_lines.append((i, line.rstrip()))
    except Exception:
        pass
    return sorry_lines


def build_file(args: tuple[Path, Path]) -> tuple[Path, bool, str, float]:
    """
    Build a single Lean file using lake lean.
    Returns (filepath, success, error_message, elapsed_seconds).
    Also reports an error if the file contains incomplete-proof markers.
    """
    root, filepath = args
    start_time = time.time()
    try:
        result = subprocess.run(
            ["lake", "lean", str(filepath)],
            cwd=root,
            capture_output=True,
            text=True,
            timeout=300,  # 5 minute timeout
        )
        elapsed = time.time() - start_time
        if result.returncode == 0:
            # Check for incomplete-proof markers.
            sorry_lines = check_for_sorry(filepath)
            if sorry_lines:
                error_msg = f"File contains '{LEAN_INCOMPLETE_TERM}' statements:\n"
                for line_num, line_content in sorry_lines:
                    error_msg += f"  Line {line_num}: {line_content}\n"
                return filepath, False, error_msg.strip(), elapsed
            return filepath, True, "", elapsed
        else:
            # Combine stdout and stderr for error output
            error = result.stderr or result.stdout or "Unknown error"
            return filepath, False, error.strip(), elapsed
    except subprocess.TimeoutExpired:
        elapsed = time.time() - start_time
        return filepath, False, "Build timed out after 5 minutes", elapsed
    except Exception as e:
        elapsed = time.time() - start_time
        return filepath, False, str(e), elapsed


def get_theorem_files(root: Path) -> list[Path]:
    """Get all theorem files in the proofs directory, excluding Spec.lean"""
    proofs_path = root / PROOFS_DIR
    files = sorted(proofs_path.glob("*.lean"))
    return [f for f in files if f.name not in EXCLUDED_FILES]


def format_error(error: str) -> str:
    """Format error message with indentation"""
    lines = error.split("\n")
    # Indent each line
    return "\n".join("       " + line for line in lines)


def format_time(seconds: float) -> str:
    """Format elapsed time in a human-readable way"""
    if seconds < 60:
        return f"{seconds:.1f}s"
    else:
        minutes = int(seconds // 60)
        secs = seconds % 60
        return f"{minutes}m {secs:.1f}s"


def parse_theorem_name(filename: str) -> tuple[str, str] | None:
    """
    Parse a theorem filename into (action, invariant).
    E.g., "Phase1a_TypeOK.lean" -> ("Phase1a", "TypeOK")
    """
    name = filename.replace(".lean", "")
    for action in ACTIONS:
        if name.startswith(action + "_"):
            invariant = name[len(action) + 1:]
            return action, invariant
    return None


def print_summary_table(results: dict[Path, bool]):
    """
    Print a matrix showing pass/error for each action/invariant combination.
    """
    # Build results matrix
    matrix: dict[str, dict[str, bool | None]] = {
        action: {inv: None for inv in INVARIANTS} for action in ACTIONS
    }

    for filepath, success in results.items():
        parsed = parse_theorem_name(filepath.name)
        if parsed:
            action, invariant = parsed
            if action in matrix and invariant in matrix[action]:
                matrix[action][invariant] = success

    # Calculate column widths
    inv_widths = {inv: max(len(inv), 4) for inv in INVARIANTS}
    action_width = max(len(a) for a in ACTIONS)

    # Print header
    print("\nResults Matrix:")
    print()
    header = " " * (action_width + 2)
    for inv in INVARIANTS:
        header += f" {inv[:inv_widths[inv]]:^{inv_widths[inv]}}"
    print(header)

    # Print separator
    sep = "-" * (action_width + 2)
    for inv in INVARIANTS:
        sep += "-" + "-" * inv_widths[inv]
    print(sep)

    # Print rows
    for action in ACTIONS:
        row = f"{action:<{action_width}} |"
        for inv in INVARIANTS:
            result = matrix[action][inv]
            if result is None:
                symbol = " - "
            elif result:
                symbol = " ✓ "  # pass
            else:
                symbol = " ✗ "  # error
            row += f" {symbol:^{inv_widths[inv]-1}}"
        print(row)

    # Print legend
    print()
    print("Legend: ✓ = pass, ✗ = error, - = not found")


def build_single_file(root: Path, filepath: Path):
    """Build a single file and print full output"""
    print(f"Building {filepath.name}...")
    print()

    _, success, error, elapsed = build_file((root, filepath))

    if success:
        print(f"[PASS] {filepath.name} ({format_time(elapsed)})")
        sys.exit(0)
    else:
        print(f"[FAIL] {filepath.name} ({format_time(elapsed)})")
        if error:
            print()
            print(error)
        sys.exit(1)


def build_all_files(root: Path):
    """Build all theorem files in parallel and report summary"""
    files = get_theorem_files(root)

    if not files:
        print("No theorem files found")
        sys.exit(1)

    print(f"Building {len(files)} theorem files in parallel (using {MAX_WORKERS} workers)...")
    print()

    passed = []
    failed = []
    timings = []  # (filepath, elapsed) for sorting at the end
    results = {}  # filepath -> success for the summary table
    total_start = time.time()

    # Build all files in parallel
    with ProcessPoolExecutor(max_workers=MAX_WORKERS) as executor:
        # Submit all build tasks
        futures = {executor.submit(build_file, (root, f)): f for f in files}

        # Process results as they complete
        for future in as_completed(futures):
            filepath, success, error, elapsed = future.result()
            timings.append((filepath, elapsed))
            results[filepath] = success

            if success:
                print(f"[PASS] {filepath.name} ({format_time(elapsed)})")
                passed.append(filepath)
            else:
                print(f"[FAIL] {filepath.name} ({format_time(elapsed)})")
                if error:
                    print(format_error(error))
                print()
                failed.append((filepath, error))

    total_elapsed = time.time() - total_start

    # Print summary
    print()
    print("=" * 55)
    print(f"Summary: {len(passed)} passed, {len(failed)} failed")
    print(f"Total wall time: {format_time(total_elapsed)}")
    print("=" * 55)

    if failed:
        print("\nFailed files:")
        for filepath, _ in sorted(failed, key=lambda x: x[0].name):
            print(f"  - {filepath.name}")

    # Print slowest files
    timings.sort(key=lambda x: x[1], reverse=True)
    print("\nSlowest files:")
    for filepath, elapsed in timings[:5]:
        print(f"  {format_time(elapsed):>10}  {filepath.name}")

    # Print summary table
    print_summary_table(results)

    if failed:
        sys.exit(1)
    else:
        sys.exit(0)


def main():
    root = find_project_root()

    if len(sys.argv) > 1:
        # Build single file
        filepath = Path(sys.argv[1])
        if not filepath.is_absolute():
            filepath = root / filepath
        if not filepath.exists():
            print(f"Error: File not found: {filepath}")
            sys.exit(1)
        build_single_file(root, filepath)
    else:
        # Build all files in parallel
        build_all_files(root)


if __name__ == "__main__":
    main()
