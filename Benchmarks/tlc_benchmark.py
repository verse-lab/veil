#!/usr/bin/env python3
"""
TLC Model Checker Benchmarking Framework

This script systematically measures running time, memory consumption,
and state space statistics when running TLC on TLA+ specifications.

Features:
- Multiple specs with multiple configurations
- Multi-threaded execution support
- Periodic progress tracking for plotting
- Memory monitoring via psutil
- JSON/CSV output for analysis
- Timeout handling

Usage:
    python tlc_benchmark.py --config benchmark_config.yaml
    python tlc_benchmark.py --spec MySpec.tla --cfg MC.cfg --workers 4
"""

import argparse
import subprocess
import re
import time
import json
import csv
import os
import sys
import signal
import threading
from datetime import datetime
from pathlib import Path
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Optional, Any
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeoutError

try:
    import psutil
    PSUTIL_AVAILABLE = True
except ImportError:
    PSUTIL_AVAILABLE = False
    print("Warning: psutil not installed. Memory tracking will be limited.")
    print("Install with: pip install psutil")

try:
    import yaml
    YAML_AVAILABLE = True
except ImportError:
    YAML_AVAILABLE = False
    print("Warning: PyYAML not installed. Using JSON config only.")
    print("Install with: pip install pyyaml")


@dataclass
class ProgressPoint:
    """A single progress measurement point from TLC."""
    timestamp: float  # seconds since start
    states_generated: int
    distinct_states: int
    states_in_queue: int
    depth: Optional[int] = None
    memory_mb: Optional[float] = None


@dataclass
class BenchmarkResult:
    """Complete benchmark result for a single TLC run."""
    spec_file: str
    config_file: str
    workers: int
    heap_size: str
    
    # Timing
    wall_time_seconds: float = 0.0
    tlc_reported_time: Optional[str] = None
    start_time: Optional[str] = None
    end_time: Optional[str] = None
    
    # State space
    states_generated: int = 0
    distinct_states: int = 0
    states_in_queue: int = 0
    depth: int = 0
    
    # Memory
    peak_memory_mb: float = 0.0
    jvm_heap_mb: Optional[float] = None
    
    # Status
    success: bool = False
    timeout: bool = False
    error_message: Optional[str] = None
    exit_code: Optional[int] = None
    
    # Progress tracking
    progress_points: List[Dict] = field(default_factory=list)
    
    # Metadata
    tlc_version: Optional[str] = None
    java_version: Optional[str] = None
    hostname: Optional[str] = None
    cpu_count: Optional[int] = None
    
    def to_dict(self) -> Dict:
        """Convert to dictionary for JSON serialization."""
        return asdict(self)


class MemoryMonitor:
    """Monitor memory usage of a process in a background thread."""
    
    def __init__(self, pid: int, interval: float = 0.5):
        self.pid = pid
        self.interval = interval
        self.peak_memory_mb = 0.0
        self.memory_samples: List[tuple] = []  # (timestamp, memory_mb)
        self._stop_event = threading.Event()
        self._thread: Optional[threading.Thread] = None
    
    def start(self):
        """Start monitoring in background thread."""
        if not PSUTIL_AVAILABLE:
            return
        self._stop_event.clear()
        self._thread = threading.Thread(target=self._monitor_loop, daemon=True)
        self._thread.start()
    
    def stop(self) -> float:
        """Stop monitoring and return peak memory."""
        self._stop_event.set()
        if self._thread:
            self._thread.join(timeout=2.0)
        return self.peak_memory_mb
    
    def _monitor_loop(self):
        """Background monitoring loop."""
        start_time = time.time()
        try:
            process = psutil.Process(self.pid)
            while not self._stop_event.is_set():
                try:
                    # Get memory of process and all children (JVM spawns threads)
                    mem = process.memory_info().rss
                    for child in process.children(recursive=True):
                        try:
                            mem += child.memory_info().rss
                        except (psutil.NoSuchProcess, psutil.AccessDenied):
                            pass
                    
                    mem_mb = mem / (1024 * 1024)
                    self.peak_memory_mb = max(self.peak_memory_mb, mem_mb)
                    self.memory_samples.append((time.time() - start_time, mem_mb))
                    
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    break
                
                self._stop_event.wait(self.interval)
        except Exception as e:
            print(f"Memory monitor error: {e}")


class TLCOutputParser:
    """Parse TLC output and extract metrics."""
    
    # Regex patterns for TLC output
    PATTERNS = {
        'version': re.compile(r'TLC2 Version ([\d.]+)'),
        'java_info': re.compile(r'\(.*?(Java|OpenJDK|AdoptOpenJDK)[^)]*\)'),
        'heap_info': re.compile(r'with (\d+)MB heap'),
        'workers_info': re.compile(r'with (\d+) worker'),
        'initial_states': re.compile(r'Finished computing initial states: (\d+) distinct'),
        'progress': re.compile(
            r'Progress\((\d+)\) at [^:]+: (\d+) states generated, '
            r'(\d+) distinct states found, (\d+) states left on queue'
        ),
        'final_states': re.compile(
            r'(\d+) states generated, (\d+) distinct states found, '
            r'(\d+) states left on queue'
        ),
        'depth': re.compile(r'depth of the complete state graph search is (\d+)'),
        'finished_time': re.compile(r'Finished in (.+?) at'),
        'error': re.compile(r'Error: (.+)'),
        'invariant_violated': re.compile(r'Invariant (.+) is violated'),
        'property_violated': re.compile(r'Temporal properties were violated'),
        'deadlock': re.compile(r'deadlock reached'),
        'success': re.compile(r'Model checking completed\. No error has been found'),
    }
    
    def __init__(self):
        self.progress_points: List[ProgressPoint] = []
        self.start_time: float = 0
    
    def set_start_time(self, start_time: float):
        """Set the benchmark start time for relative timestamps."""
        self.start_time = start_time
    
    def parse_line(self, line: str, current_memory_mb: Optional[float] = None) -> Optional[ProgressPoint]:
        """Parse a single line of TLC output, return ProgressPoint if it's a progress line."""
        progress_match = self.PATTERNS['progress'].search(line)
        if progress_match:
            point = ProgressPoint(
                timestamp=time.time() - self.start_time,
                depth=int(progress_match.group(1)),
                states_generated=int(progress_match.group(2)),
                distinct_states=int(progress_match.group(3)),
                states_in_queue=int(progress_match.group(4)),
                memory_mb=current_memory_mb
            )
            self.progress_points.append(point)
            return point
        return None
    
    def parse_full_output(self, output: str) -> Dict[str, Any]:
        """Parse complete TLC output and extract all metrics."""
        result = {
            'tlc_version': None,
            'jvm_heap_mb': None,
            'states_generated': 0,
            'distinct_states': 0,
            'states_in_queue': 0,
            'depth': 0,
            'tlc_reported_time': None,
            'success': False,
            'error_message': None,
            'invariant_violated': None,
            'deadlock': False,
        }
        
        # Version
        match = self.PATTERNS['version'].search(output)
        if match:
            result['tlc_version'] = match.group(1)
        
        # Heap info
        match = self.PATTERNS['heap_info'].search(output)
        if match:
            result['jvm_heap_mb'] = int(match.group(1))
        
        # Final states (last occurrence)
        for match in self.PATTERNS['final_states'].finditer(output):
            result['states_generated'] = int(match.group(1))
            result['distinct_states'] = int(match.group(2))
            result['states_in_queue'] = int(match.group(3))
        
        # Depth
        match = self.PATTERNS['depth'].search(output)
        if match:
            result['depth'] = int(match.group(1))
        
        # Finished time
        match = self.PATTERNS['finished_time'].search(output)
        if match:
            result['tlc_reported_time'] = match.group(1)
        
        # Success
        if self.PATTERNS['success'].search(output):
            result['success'] = True
        
        # Errors
        error_match = self.PATTERNS['error'].search(output)
        if error_match:
            result['error_message'] = error_match.group(1)
        
        inv_match = self.PATTERNS['invariant_violated'].search(output)
        if inv_match:
            result['invariant_violated'] = inv_match.group(1)
            result['error_message'] = f"Invariant {inv_match.group(1)} violated"
        
        if self.PATTERNS['property_violated'].search(output):
            result['error_message'] = "Temporal properties violated"
        
        if self.PATTERNS['deadlock'].search(output):
            result['deadlock'] = True
            result['error_message'] = "Deadlock reached"
        
        return result


class TLCBenchmark:
    """Main benchmarking class for TLC."""
    
    DEFAULT_JAVA_OPTS = [
        "-XX:+UseParallelGC",
        "-XX:+IgnoreUnrecognizedVMOptions",
    ]
    
    def __init__(self, 
                 tla2tools_jar: str = "tla2tools.jar",
                 java_cmd: str = "java",
                 output_dir: str = "benchmark_results",
                 verbose: bool = True):
        self.tla2tools_jar = tla2tools_jar
        self.java_cmd = java_cmd
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.verbose = verbose
        
        # System info
        self.hostname = os.uname().nodename if hasattr(os, 'uname') else "unknown"
        self.cpu_count = os.cpu_count() or 1
    
    def log(self, message: str):
        """Print message if verbose mode is enabled."""
        if self.verbose:
            print(f"[{datetime.now().strftime('%H:%M:%S')}] {message}")
    
    def build_command(self, 
                      spec_file: str,
                      config_file: Optional[str] = None,
                      workers: int = 1,
                      heap_size: str = "4G",
                      extra_opts: Optional[List[str]] = None) -> List[str]:
        """Build the TLC command line."""
        cmd = [
            self.java_cmd,
            f"-Xms{heap_size}",
            f"-Xmx{heap_size}",
            *self.DEFAULT_JAVA_OPTS,
            "-jar", self.tla2tools_jar,
            "-workers", str(workers),
            "-cleanup",
        ]
        
        if config_file:
            cmd.extend(["-config", config_file])
        
        if extra_opts:
            cmd.extend(extra_opts)
        
        cmd.append(spec_file)
        
        return cmd
    
    def run_single(self,
                   spec_file: str,
                   config_file: Optional[str] = None,
                   workers: int = 1,
                   heap_size: str = "4G",
                   timeout_seconds: int = 3600,
                   extra_opts: Optional[List[str]] = None,
                   working_dir: Optional[str] = None) -> BenchmarkResult:
        """Run a single TLC benchmark."""
        
        result = BenchmarkResult(
            spec_file=spec_file,
            config_file=config_file or "default",
            workers=workers,
            heap_size=heap_size,
            hostname=self.hostname,
            cpu_count=self.cpu_count,
        )
        
        cmd = self.build_command(spec_file, config_file, workers, heap_size, extra_opts)
        
        self.log(f"Running: {' '.join(cmd)}")
        self.log(f"Timeout: {timeout_seconds}s, Workers: {workers}, Heap: {heap_size}")
        
        parser = TLCOutputParser()
        output_lines = []
        
        result.start_time = datetime.now().isoformat()
        start_time = time.time()
        parser.set_start_time(start_time)
        
        try:
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
                cwd=working_dir
            )
            
            # Start memory monitoring
            memory_monitor = MemoryMonitor(process.pid)
            memory_monitor.start()
            
            # Read output line by line for progress tracking
            try:
                while True:
                    line = process.stdout.readline()
                    if not line and process.poll() is not None:
                        break
                    
                    if line:
                        output_lines.append(line)
                        if self.verbose and ("Progress" in line or "Error" in line or "Finished" in line):
                            print(f"  {line.rstrip()}")
                        
                        # Parse progress
                        current_mem = memory_monitor.peak_memory_mb
                        parser.parse_line(line, current_mem)
                    
                    # Check timeout
                    if time.time() - start_time > timeout_seconds:
                        self.log(f"Timeout reached ({timeout_seconds}s), terminating...")
                        process.terminate()
                        try:
                            process.wait(timeout=10)
                        except subprocess.TimeoutExpired:
                            process.kill()
                        result.timeout = True
                        break
                        
            except Exception as e:
                self.log(f"Error reading output: {e}")
            
            # Wait for process to complete
            try:
                process.wait(timeout=30)
            except subprocess.TimeoutExpired:
                process.kill()
            
            result.exit_code = process.returncode
            
            # Stop memory monitoring
            result.peak_memory_mb = memory_monitor.stop()
            
        except FileNotFoundError as e:
            result.error_message = f"Command not found: {e}"
            self.log(f"Error: {result.error_message}")
            return result
        except Exception as e:
            result.error_message = str(e)
            self.log(f"Error: {result.error_message}")
            return result
        
        result.end_time = datetime.now().isoformat()
        result.wall_time_seconds = time.time() - start_time
        
        # Parse complete output
        full_output = ''.join(output_lines)
        parsed = parser.parse_full_output(full_output)
        
        result.tlc_version = parsed['tlc_version']
        result.jvm_heap_mb = parsed['jvm_heap_mb']
        result.states_generated = parsed['states_generated']
        result.distinct_states = parsed['distinct_states']
        result.states_in_queue = parsed['states_in_queue']
        result.depth = parsed['depth']
        result.tlc_reported_time = parsed['tlc_reported_time']
        result.success = parsed['success']
        
        if not result.timeout and parsed['error_message']:
            result.error_message = parsed['error_message']
        
        # Store progress points
        result.progress_points = [asdict(p) for p in parser.progress_points]
        
        self.log(f"Completed: {result.distinct_states} distinct states, "
                f"{result.wall_time_seconds:.2f}s, {result.peak_memory_mb:.1f}MB peak")
        
        return result
    
    def run_batch(self, 
                  benchmarks: List[Dict],
                  repetitions: int = 1,
                  save_intermediate: bool = True) -> List[BenchmarkResult]:
        """Run a batch of benchmarks."""
        all_results = []
        total = len(benchmarks) * repetitions
        current = 0
        
        for bench in benchmarks:
            for rep in range(repetitions):
                current += 1
                self.log(f"\n{'='*60}")
                self.log(f"Benchmark {current}/{total}: {bench.get('spec_file', 'unknown')} "
                        f"(rep {rep+1}/{repetitions})")
                self.log('='*60)
                
                result = self.run_single(
                    spec_file=bench['spec_file'],
                    config_file=bench.get('config_file'),
                    workers=bench.get('workers', 1),
                    heap_size=bench.get('heap_size', '4G'),
                    timeout_seconds=bench.get('timeout_seconds', 3600),
                    extra_opts=bench.get('extra_opts'),
                    working_dir=bench.get('working_dir'),
                )
                
                # Add benchmark metadata
                result_dict = result.to_dict()
                result_dict['benchmark_name'] = bench.get('name', bench['spec_file'])
                result_dict['repetition'] = rep + 1
                
                all_results.append(result)
                
                if save_intermediate:
                    self._save_results(all_results, "intermediate_results.json")
        
        return all_results
    
    def _save_results(self, results: List[BenchmarkResult], filename: str):
        """Save results to JSON file."""
        filepath = self.output_dir / filename
        data = [r.to_dict() if isinstance(r, BenchmarkResult) else r for r in results]
        with open(filepath, 'w') as f:
            json.dump(data, f, indent=2, default=str)
    
    def save_results(self, 
                     results: List[BenchmarkResult],
                     base_name: str = "benchmark_results"):
        """Save results in multiple formats."""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        
        # JSON with full details
        json_file = self.output_dir / f"{base_name}_{timestamp}.json"
        data = [r.to_dict() if isinstance(r, BenchmarkResult) else r for r in results]
        with open(json_file, 'w') as f:
            json.dump(data, f, indent=2, default=str)
        self.log(f"Saved JSON results to: {json_file}")
        
        # CSV summary
        csv_file = self.output_dir / f"{base_name}_{timestamp}.csv"
        if results:
            fieldnames = [
                'spec_file', 'config_file', 'workers', 'heap_size',
                'wall_time_seconds', 'tlc_reported_time',
                'states_generated', 'distinct_states', 'depth',
                'peak_memory_mb', 'success', 'timeout', 'error_message'
            ]
            with open(csv_file, 'w', newline='') as f:
                writer = csv.DictWriter(f, fieldnames=fieldnames, extrasaction='ignore')
                writer.writeheader()
                for r in results:
                    row = r.to_dict() if isinstance(r, BenchmarkResult) else r
                    writer.writerow(row)
            self.log(f"Saved CSV summary to: {csv_file}")
        
        # Progress data for plotting (separate file)
        progress_file = self.output_dir / f"{base_name}_{timestamp}_progress.json"
        progress_data = []
        for i, r in enumerate(results):
            rd = r.to_dict() if isinstance(r, BenchmarkResult) else r
            if rd.get('progress_points'):
                progress_data.append({
                    'spec_file': rd['spec_file'],
                    'config_file': rd['config_file'],
                    'workers': rd['workers'],
                    'progress_points': rd['progress_points']
                })
        
        if progress_data:
            with open(progress_file, 'w') as f:
                json.dump(progress_data, f, indent=2)
            self.log(f"Saved progress data to: {progress_file}")
        
        return json_file, csv_file


def load_config(config_file: str) -> Dict:
    """Load benchmark configuration from YAML or JSON file."""
    with open(config_file, 'r') as f:
        if config_file.endswith('.yaml') or config_file.endswith('.yml'):
            if not YAML_AVAILABLE:
                raise ImportError("PyYAML required for .yaml config files")
            return yaml.safe_load(f)
        else:
            return json.load(f)


def main():
    parser = argparse.ArgumentParser(
        description="TLC Model Checker Benchmarking Framework",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Single spec benchmark
  python tlc_benchmark.py --spec MySpec.tla --cfg MC.cfg --workers 4

  # Batch benchmark from config file
  python tlc_benchmark.py --config benchmark_config.yaml

  # With custom settings
  python tlc_benchmark.py --spec MySpec.tla --heap 8G --timeout 7200 --reps 3
        """
    )
    
    # Config file mode
    parser.add_argument('--config', '-c', type=str,
                        help='Configuration file (YAML or JSON)')
    
    # Single run mode
    parser.add_argument('--spec', '-s', type=str,
                        help='TLA+ specification file')
    parser.add_argument('--cfg', type=str,
                        help='TLC configuration file')
    parser.add_argument('--workers', '-w', type=int, default=1,
                        help='Number of worker threads (default: 1)')
    parser.add_argument('--heap', type=str, default='4G',
                        help='JVM heap size (default: 4G)')
    parser.add_argument('--timeout', '-t', type=int, default=3600,
                        help='Timeout in seconds (default: 3600)')
    
    # Common options
    parser.add_argument('--jar', type=str, default='tla2tools.jar',
                        help='Path to tla2tools.jar')
    parser.add_argument('--java', type=str, default='java',
                        help='Java command (default: java)')
    parser.add_argument('--output', '-o', type=str, default='benchmark_results',
                        help='Output directory (default: benchmark_results)')
    parser.add_argument('--reps', '-r', type=int, default=1,
                        help='Number of repetitions (default: 1)')
    parser.add_argument('--quiet', '-q', action='store_true',
                        help='Quiet mode (less output)')
    
    args = parser.parse_args()
    
    # Initialize benchmark runner
    benchmark = TLCBenchmark(
        tla2tools_jar=args.jar,
        java_cmd=args.java,
        output_dir=args.output,
        verbose=not args.quiet
    )
    
    if args.config:
        # Batch mode from config file
        config = load_config(args.config)
        
        # Global settings
        global_settings = config.get('global', {})
        if 'tla2tools_jar' in global_settings:
            benchmark.tla2tools_jar = global_settings['tla2tools_jar']
        if 'java_cmd' in global_settings:
            benchmark.java_cmd = global_settings['java_cmd']
        
        benchmarks = config.get('benchmarks', [])
        repetitions = config.get('repetitions', args.reps)
        
        results = benchmark.run_batch(benchmarks, repetitions=repetitions)
        
    elif args.spec:
        # Single run mode
        benchmarks = [{
            'spec_file': args.spec,
            'config_file': args.cfg,
            'workers': args.workers,
            'heap_size': args.heap,
            'timeout_seconds': args.timeout,
        }]
        results = benchmark.run_batch(benchmarks, repetitions=args.reps)
        
    else:
        parser.print_help()
        sys.exit(1)
    
    # Save results
    benchmark.save_results(results)
    
    # Print summary
    print("\n" + "="*60)
    print("BENCHMARK SUMMARY")
    print("="*60)
    
    for r in results:
        rd = r.to_dict() if isinstance(r, BenchmarkResult) else r
        status = "✓" if rd['success'] else ("⏱" if rd['timeout'] else "✗")
        print(f"{status} {rd['spec_file']} ({rd['config_file']})")
        print(f"   Workers: {rd['workers']}, Time: {rd['wall_time_seconds']:.2f}s, "
              f"States: {rd['distinct_states']}, Memory: {rd['peak_memory_mb']:.1f}MB")
        if rd.get('error_message'):
            print(f"   Error: {rd['error_message']}")
    
    print("="*60)


if __name__ == "__main__":
    main()
