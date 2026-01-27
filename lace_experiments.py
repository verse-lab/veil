#!/usr/bin/env python3
"""
Experiment runner script for model checker benchmarks.

Usage:
    python run_experiments.py -n <n> -m <m> <experiment_names...>

Example:
    python run_experiments.py -n 4 -m 8 TwoPhaseCommit-8 EWD840-5
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional


@dataclass
class ResourceUsage:
    """Resource usage statistics from a process run."""
    user_time_seconds: float = 0.0
    system_time_seconds: float = 0.0
    max_rss_bytes: int = 0  # maximum resident set size
    peak_memory_footprint_bytes: int = 0  # macOS-specific, closer to Activity Monitor

    @property
    def max_rss_mb(self) -> float:
        return self.max_rss_bytes / (1024 * 1024)

    @property
    def peak_memory_mb(self) -> float:
        """Peak memory footprint in MB (matches Activity Monitor)."""
        return self.peak_memory_footprint_bytes / (1024 * 1024)

    @property
    def cpu_time_seconds(self) -> float:
        return self.user_time_seconds + self.system_time_seconds


@dataclass
class ExperimentResult:
    """Result of a single experiment run."""
    name: str
    compilation_time_seconds: float
    execution_time_seconds: float
    stdout: str
    stderr: str
    parsed_output: Optional[dict] = None
    compilation_success: bool = True
    execution_success: bool = True
    resource_usage: ResourceUsage = field(default_factory=ResourceUsage)


def parse_model_checker_output(output: str) -> Optional[dict]:
    """
    Parse the model checker output.

    The output consists of multiple JSON lines. We extract:
    - The final result line (contains termination_reason, result, explored_states)
    - The last progress update (contains detailed stats)

    Returns a dict with the parsed information.
    """
    lines = output.strip().split('\n')
    if not lines:
        return None

    result = {
        'progress_updates': [],
        'final_result': None,
        'last_progress': None,
    }

    for line in lines:
        line = line.strip()
        if not line:
            continue
        try:
            data = json.loads(line)
            # Check if this is the final result line
            if 'termination_reason' in data or 'result' in data:
                result['final_result'] = data
            else:
                result['progress_updates'].append(data)
                result['last_progress'] = data
        except json.JSONDecodeError:
            # Skip non-JSON lines
            continue

    return result


def parse_time_output(stderr: str) -> ResourceUsage:
    """
    Parse the output from /usr/bin/time -lp to extract resource usage.

    macOS /usr/bin/time -lp output format:
        real         1.23
        user         0.98
        sys          0.12
              12345678  maximum resident set size
              ...
              12345678  peak memory footprint
    """
    usage = ResourceUsage()

    # Parse real/user/sys times (POSIX format from -p)
    user_match = re.search(r'^user\s+([\d.]+)', stderr, re.MULTILINE)
    sys_match = re.search(r'^sys\s+([\d.]+)', stderr, re.MULTILINE)

    if user_match:
        usage.user_time_seconds = float(user_match.group(1))
    if sys_match:
        usage.system_time_seconds = float(sys_match.group(1))

    # Parse maximum resident set size (in bytes on macOS)
    rss_match = re.search(r'(\d+)\s+maximum resident set size', stderr)
    if rss_match:
        usage.max_rss_bytes = int(rss_match.group(1))

    # Parse peak memory footprint (macOS-specific, closer to Activity Monitor)
    footprint_match = re.search(r'(\d+)\s+peak memory footprint', stderr)
    if footprint_match:
        usage.peak_memory_footprint_bytes = int(footprint_match.group(1))

    return usage


def run_experiment(name: str, n: int, m: int, base_dir: Path) -> ExperimentResult:
    """
    Run a single experiment.

    Steps:
    1. Delete the .lake directory under the experiment
    2. Run `lake build ModelCheckerMain` and measure compilation time
    3. Run the model checker binary and measure execution time
    """
    experiment_dir = base_dir / ".lake" / "model_checker_builds" / name
    lake_dir = experiment_dir / ".lake"
    binary_path = base_dir / ".lake" / "model_checker_builds" / name / ".lake" / "build" / "bin" / "ModelCheckerMain"

    result = ExperimentResult(
        name=name,
        compilation_time_seconds=0.0,
        execution_time_seconds=0.0,
        stdout="",
        stderr="",
    )

    # Check if experiment directory exists
    if not experiment_dir.exists():
        print(f"  [ERROR] Experiment directory does not exist: {experiment_dir}")
        result.compilation_success = False
        result.execution_success = False
        return result

    # Step 1: Delete the .lake directory under the experiment
    if lake_dir.exists():
        print(f"  Deleting {lake_dir}...")
        shutil.rmtree(lake_dir)

    # Step 2: Run `lake build ModelCheckerMain` and measure compilation time
    compile_cmd = ["lake", "build", "ModelCheckerMain"]
    print(f"  Command: cd {experiment_dir} && {' '.join(compile_cmd)}")
    start_time = time.perf_counter()
    try:
        compile_result = subprocess.run(
            compile_cmd,
            cwd=experiment_dir,
            capture_output=True,
            text=True,
        )
        end_time = time.perf_counter()
        result.compilation_time_seconds = end_time - start_time

        if compile_result.returncode != 0:
            print(f"  [ERROR] Compilation failed!")
            print(f"  stdout: {compile_result.stdout}")
            print(f"  stderr: {compile_result.stderr}")
            result.compilation_success = False
            result.execution_success = False
            return result

        print(f"  Compilation completed in {result.compilation_time_seconds:.2f}s")
    except Exception as e:
        print(f"  [ERROR] Failed to run compilation: {e}")
        result.compilation_success = False
        result.execution_success = False
        return result

    # Step 3: Run the model checker binary with /usr/bin/time for resource measurement
    if not binary_path.exists():
        print(f"  [ERROR] Binary does not exist: {binary_path}")
        result.execution_success = False
        return result

    # Use /usr/bin/time -lp to measure CPU time and memory usage
    # -l: detailed resource usage (includes max resident set size)
    # -p: POSIX output format (easier to parse)
    run_cmd = ["/usr/bin/time", "-lp", str(binary_path), str(n), str(m)]
    print(f"  Command: {' '.join(run_cmd)}")
    start_time = time.perf_counter()
    try:
        run_result = subprocess.run(
            run_cmd,
            capture_output=True,
            text=True,
        )
        end_time = time.perf_counter()
        result.execution_time_seconds = end_time - start_time

        # /usr/bin/time outputs to stderr, along with the program's stderr
        # The program's stdout goes to stdout
        result.stdout = run_result.stdout
        result.stderr = run_result.stderr

        # Parse resource usage from time output (which is in stderr)
        result.resource_usage = parse_time_output(run_result.stderr)

        if run_result.returncode != 0:
            print(f"  [WARNING] Model checker exited with non-zero code: {run_result.returncode}")
            result.execution_success = False

        print(f"  Execution completed in {result.execution_time_seconds:.2f}s")
        print(f"  CPU time: {result.resource_usage.cpu_time_seconds:.2f}s (user: {result.resource_usage.user_time_seconds:.2f}s, sys: {result.resource_usage.system_time_seconds:.2f}s)")
        print(f"  Peak memory: {result.resource_usage.peak_memory_mb:.2f} MB (footprint), {result.resource_usage.max_rss_mb:.2f} MB (RSS)")

        # Parse the model checker output
        combined_output = result.stdout + result.stderr
        result.parsed_output = parse_model_checker_output(combined_output)

    except Exception as e:
        print(f"  [ERROR] Failed to run model checker: {e}")
        result.execution_success = False

    return result


def print_summary(results: list[ExperimentResult]):
    """Print a summary of all experiment results."""
    print("\n" + "=" * 120)
    print("EXPERIMENT SUMMARY")
    print("=" * 120)

    print(f"\n{'Experiment':<30} {'Compile(s)':<12} {'Exec(s)':<10} {'CPU(s)':<10} {'Mem(MB)':<12} {'Status':<8} {'Result'}")
    print("-" * 120)

    for r in results:
        status = "OK" if (r.compilation_success and r.execution_success) else "FAILED"
        final_result = ""
        if r.parsed_output and r.parsed_output.get('final_result'):
            final = r.parsed_output['final_result']
            final_result = final.get('result', '')

        print(f"{r.name:<30} {r.compilation_time_seconds:<12.2f} {r.execution_time_seconds:<10.2f} "
              f"{r.resource_usage.cpu_time_seconds:<10.2f} {r.resource_usage.peak_memory_mb:<12.2f} "
              f"{status:<8} {final_result}")

    print("-" * 120)

    total_compile = sum(r.compilation_time_seconds for r in results)
    total_execute = sum(r.execution_time_seconds for r in results)
    total_cpu = sum(r.resource_usage.cpu_time_seconds for r in results)
    max_memory = max((r.resource_usage.peak_memory_mb for r in results), default=0)
    print(f"{'TOTAL/MAX':<30} {total_compile:<12.2f} {total_execute:<10.2f} {total_cpu:<10.2f} {max_memory:<12.2f}")


def export_results_json(results: list[ExperimentResult], output_file: str):
    """Export results to a JSON file."""
    data = []
    for r in results:
        entry = {
            'name': r.name,
            'compilation_time_seconds': r.compilation_time_seconds,
            'execution_time_seconds': r.execution_time_seconds,
            'compilation_success': r.compilation_success,
            'execution_success': r.execution_success,
            'user_time_seconds': r.resource_usage.user_time_seconds,
            'system_time_seconds': r.resource_usage.system_time_seconds,
            'cpu_time_seconds': r.resource_usage.cpu_time_seconds,
            'max_rss_bytes': r.resource_usage.max_rss_bytes,
            'max_rss_mb': r.resource_usage.max_rss_mb,
            'peak_memory_footprint_bytes': r.resource_usage.peak_memory_footprint_bytes,
            'peak_memory_mb': r.resource_usage.peak_memory_mb,  # footprint, matches Activity Monitor
        }
        if r.parsed_output:
            if r.parsed_output.get('final_result'):
                entry['final_result'] = r.parsed_output['final_result']
            if r.parsed_output.get('last_progress'):
                last = r.parsed_output['last_progress']
                entry['distinct_states'] = last.get('distinctStates')
                entry['states_found'] = last.get('statesFound')
                entry['diameter'] = last.get('diameter')
                entry['elapsed_ms'] = last.get('elapsedMs')
        data.append(entry)

    with open(output_file, 'w') as f:
        json.dump(data, f, indent=2)
    print(f"\nResults exported to: {output_file}")


def main():
    parser = argparse.ArgumentParser(
        description="Run model checker experiments",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python run_experiments.py -n 4 -m 8 TwoPhaseCommit-8 EWD840-5
    python run_experiments.py -n 2 -m 4 -o results.json TwoPhaseCommit-8
        """
    )
    parser.add_argument('-n', type=int, required=True, help='First argument to ModelCheckerMain')
    parser.add_argument('-m', type=int, required=True, help='Second argument to ModelCheckerMain')
    parser.add_argument('-o', '--output', type=str, default=None, help='Output JSON file for results')
    parser.add_argument('experiments', nargs='+', help='List of experiment names')

    args = parser.parse_args()

    base_dir = Path.cwd()

    print(f"Base directory: {base_dir}")
    print(f"Parameters: n={args.n}, m={args.m}")
    print(f"Experiments: {args.experiments}")
    print()

    results = []
    for i, name in enumerate(args.experiments, 1):
        print(f"[{i}/{len(args.experiments)}] Running experiment: {name}")
        result = run_experiment(name, args.n, args.m, base_dir)
        results.append(result)
        print()

    print_summary(results)

    # Export to JSON if requested (with timestamp appended to filename)
    if args.output:
        # Add timestamp to filename to avoid overwriting
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_path = Path(args.output)
        output_file = f"{output_path.stem}_{timestamp}{output_path.suffix}"
        export_results_json(results, output_file)


if __name__ == "__main__":
    main()
