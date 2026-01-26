#!/usr/bin/env python3
"""
TLC Benchmark Analysis Script

Compute statistics from benchmark results and generate formatted output
suitable for research papers (LaTeX tables, statistical summaries).

Usage:
    python analyze_results.py benchmark_results.json
    python analyze_results.py --latex results1.json results2.json
    python analyze_results.py --aggregate-reps results.json
"""

import argparse
import json
import sys
from pathlib import Path
from typing import List, Dict, Any, Optional
from collections import defaultdict
import statistics


def load_results(filepath: str) -> List[Dict]:
    """Load benchmark results from JSON file."""
    with open(filepath, 'r') as f:
        data = json.load(f)
    return data if isinstance(data, list) else [data]


def format_number(n: float, precision: int = 2) -> str:
    """Format number with appropriate suffix (K, M, B)."""
    if n < 1000:
        return f"{n:.{precision}f}" if isinstance(n, float) else str(n)
    elif n < 1_000_000:
        return f"{n/1000:.{precision}f}K"
    elif n < 1_000_000_000:
        return f"{n/1_000_000:.{precision}f}M"
    else:
        return f"{n/1_000_000_000:.{precision}f}B"


def format_time(seconds: float) -> str:
    """Format time in human-readable format."""
    if seconds < 60:
        return f"{seconds:.1f}s"
    elif seconds < 3600:
        mins = seconds / 60
        return f"{mins:.1f}m"
    else:
        hours = seconds / 3600
        return f"{hours:.2f}h"


class BenchmarkAnalyzer:
    """Analyze benchmark results and compute statistics."""
    
    def __init__(self, results: List[Dict]):
        self.results = results
    
    def group_by_benchmark(self) -> Dict[str, List[Dict]]:
        """Group results by benchmark name/config for aggregating repetitions."""
        groups = defaultdict(list)
        for r in self.results:
            # Create a key that identifies the benchmark
            key = (
                r.get('spec_file', 'unknown'),
                r.get('config_file', 'default'),
                r.get('workers', 1),
                r.get('heap_size', '4G')
            )
            groups[key].append(r)
        return dict(groups)
    
    def compute_stats(self, values: List[float]) -> Dict[str, float]:
        """Compute statistical measures for a list of values."""
        if not values:
            return {'mean': 0, 'std': 0, 'min': 0, 'max': 0, 'median': 0, 'n': 0}
        
        n = len(values)
        mean = statistics.mean(values)
        std = statistics.stdev(values) if n > 1 else 0
        median = statistics.median(values)
        
        return {
            'mean': mean,
            'std': std,
            'min': min(values),
            'max': max(values),
            'median': median,
            'n': n
        }
    
    def aggregate_repetitions(self) -> List[Dict]:
        """Aggregate results from multiple repetitions."""
        groups = self.group_by_benchmark()
        aggregated = []
        
        for key, runs in groups.items():
            spec_file, config_file, workers, heap_size = key
            
            # Filter only successful runs for statistics
            successful = [r for r in runs if r.get('success')]
            
            if not successful:
                # All runs failed/timed out
                aggregated.append({
                    'spec_file': spec_file,
                    'config_file': config_file,
                    'workers': workers,
                    'heap_size': heap_size,
                    'total_runs': len(runs),
                    'successful_runs': 0,
                    'timeout_runs': sum(1 for r in runs if r.get('timeout')),
                    'error_runs': sum(1 for r in runs if not r.get('success') and not r.get('timeout')),
                })
                continue
            
            # Compute statistics for each metric
            time_stats = self.compute_stats([r['wall_time_seconds'] for r in successful])
            states_gen_stats = self.compute_stats([r['states_generated'] for r in successful])
            states_dist_stats = self.compute_stats([r['distinct_states'] for r in successful])
            memory_stats = self.compute_stats([r['peak_memory_mb'] for r in successful])
            
            aggregated.append({
                'spec_file': spec_file,
                'config_file': config_file,
                'workers': workers,
                'heap_size': heap_size,
                'total_runs': len(runs),
                'successful_runs': len(successful),
                'timeout_runs': sum(1 for r in runs if r.get('timeout')),
                'error_runs': sum(1 for r in runs if not r.get('success') and not r.get('timeout')),
                
                # Time statistics
                'time_mean': time_stats['mean'],
                'time_std': time_stats['std'],
                'time_min': time_stats['min'],
                'time_max': time_stats['max'],
                
                # States generated
                'states_gen_mean': states_gen_stats['mean'],
                'states_gen_std': states_gen_stats['std'],
                
                # Distinct states
                'states_dist_mean': states_dist_stats['mean'],
                'states_dist_std': states_dist_stats['std'],
                
                # Memory
                'memory_mean': memory_stats['mean'],
                'memory_std': memory_stats['std'],
                
                # Depth (assuming constant across runs)
                'depth': successful[0].get('depth', 0),
            })
        
        return aggregated
    
    def print_summary(self):
        """Print a human-readable summary of results."""
        print("\n" + "="*80)
        print("BENCHMARK RESULTS SUMMARY")
        print("="*80)
        
        aggregated = self.aggregate_repetitions()
        
        for bench in aggregated:
            print(f"\n{Path(bench['spec_file']).stem} / {Path(bench['config_file']).stem}")
            print(f"  Workers: {bench['workers']}, Heap: {bench['heap_size']}")
            print(f"  Runs: {bench['successful_runs']}/{bench['total_runs']} successful")
            
            if bench['successful_runs'] > 0:
                print(f"  Time: {bench['time_mean']:.2f}s ± {bench['time_std']:.2f}s")
                print(f"  States: {format_number(bench['states_dist_mean'])} distinct")
                print(f"  Memory: {bench['memory_mean']:.0f}MB ± {bench['memory_std']:.0f}MB")
                print(f"  Depth: {bench['depth']}")
            
            if bench['timeout_runs'] > 0:
                print(f"  Timeouts: {bench['timeout_runs']}")
            if bench['error_runs'] > 0:
                print(f"  Errors: {bench['error_runs']}")
    
    def to_latex_table(self, caption: str = "TLC Benchmark Results",
                       label: str = "tab:tlc-results") -> str:
        """Generate a LaTeX table from aggregated results."""
        aggregated = self.aggregate_repetitions()
        
        lines = []
        lines.append(r"\begin{table}[htbp]")
        lines.append(r"\centering")
        lines.append(r"\caption{" + caption + "}")
        lines.append(r"\label{" + label + "}")
        lines.append(r"\begin{tabular}{lrrrrr}")
        lines.append(r"\toprule")
        lines.append(r"Specification & Workers & Time (s) & Distinct States & Memory (MB) & Depth \\")
        lines.append(r"\midrule")
        
        for bench in aggregated:
            spec_name = Path(bench['spec_file']).stem
            # Escape underscores for LaTeX
            spec_name = spec_name.replace('_', r'\_')
            
            if bench['successful_runs'] > 0:
                time_str = f"${bench['time_mean']:.1f} \\pm {bench['time_std']:.1f}$"
                states_str = format_number(bench['states_dist_mean'])
                memory_str = f"${bench['memory_mean']:.0f}$"
                depth_str = str(bench['depth'])
            else:
                time_str = "T/O" if bench['timeout_runs'] > 0 else "Error"
                states_str = "-"
                memory_str = "-"
                depth_str = "-"
            
            lines.append(f"{spec_name} & {bench['workers']} & {time_str} & "
                        f"{states_str} & {memory_str} & {depth_str} \\\\")
        
        lines.append(r"\bottomrule")
        lines.append(r"\end{tabular}")
        lines.append(r"\end{table}")
        
        return "\n".join(lines)
    
    def to_csv(self) -> str:
        """Generate CSV output from aggregated results."""
        aggregated = self.aggregate_repetitions()
        
        headers = [
            "spec_file", "config_file", "workers", "heap_size",
            "successful_runs", "total_runs",
            "time_mean", "time_std", "time_min", "time_max",
            "states_distinct_mean", "states_distinct_std",
            "memory_mean_mb", "memory_std_mb", "depth"
        ]
        
        lines = [",".join(headers)]
        
        for bench in aggregated:
            values = [
                Path(bench['spec_file']).stem,
                Path(bench['config_file']).stem,
                str(bench['workers']),
                bench['heap_size'],
                str(bench['successful_runs']),
                str(bench['total_runs']),
                f"{bench.get('time_mean', 0):.2f}",
                f"{bench.get('time_std', 0):.2f}",
                f"{bench.get('time_min', 0):.2f}",
                f"{bench.get('time_max', 0):.2f}",
                f"{bench.get('states_dist_mean', 0):.0f}",
                f"{bench.get('states_dist_std', 0):.0f}",
                f"{bench.get('memory_mean', 0):.1f}",
                f"{bench.get('memory_std', 0):.1f}",
                str(bench.get('depth', 0))
            ]
            lines.append(",".join(values))
        
        return "\n".join(lines)
    
    def to_markdown_table(self) -> str:
        """Generate Markdown table from aggregated results."""
        aggregated = self.aggregate_repetitions()
        
        lines = []
        lines.append("| Specification | Workers | Time (s) | Distinct States | Memory (MB) | Status |")
        lines.append("|--------------|---------|----------|-----------------|-------------|--------|")
        
        for bench in aggregated:
            spec_name = Path(bench['spec_file']).stem
            
            if bench['successful_runs'] > 0:
                time_str = f"{bench['time_mean']:.1f} ± {bench['time_std']:.1f}"
                states_str = format_number(bench['states_dist_mean'])
                memory_str = f"{bench['memory_mean']:.0f}"
                status = f"✓ ({bench['successful_runs']}/{bench['total_runs']})"
            else:
                time_str = "-"
                states_str = "-"
                memory_str = "-"
                if bench['timeout_runs'] > 0:
                    status = f"⏱ Timeout ({bench['timeout_runs']})"
                else:
                    status = f"✗ Error ({bench['error_runs']})"
            
            lines.append(f"| {spec_name} | {bench['workers']} | {time_str} | "
                        f"{states_str} | {memory_str} | {status} |")
        
        return "\n".join(lines)
    
    def compute_speedup(self) -> List[Dict]:
        """Compute speedup for different worker configurations."""
        aggregated = self.aggregate_repetitions()
        
        # Group by spec/config (ignoring workers)
        spec_groups = defaultdict(list)
        for bench in aggregated:
            key = (bench['spec_file'], bench['config_file'])
            spec_groups[key].append(bench)
        
        speedup_results = []
        
        for key, benches in spec_groups.items():
            # Sort by workers
            benches.sort(key=lambda x: x['workers'])
            
            # Find baseline (single worker)
            baseline = next((b for b in benches if b['workers'] == 1), None)
            if not baseline or baseline['successful_runs'] == 0:
                continue
            
            baseline_time = baseline['time_mean']
            
            for bench in benches:
                if bench['successful_runs'] == 0:
                    continue
                
                speedup = baseline_time / bench['time_mean'] if bench['time_mean'] > 0 else 0
                efficiency = speedup / bench['workers'] if bench['workers'] > 0 else 0
                
                speedup_results.append({
                    'spec_file': bench['spec_file'],
                    'config_file': bench['config_file'],
                    'workers': bench['workers'],
                    'time_mean': bench['time_mean'],
                    'speedup': speedup,
                    'efficiency': efficiency,
                    'ideal_speedup': bench['workers'],
                })
        
        return speedup_results
    
    def print_speedup_analysis(self):
        """Print speedup analysis for multi-threaded runs."""
        speedup_data = self.compute_speedup()
        
        if not speedup_data:
            print("No speedup data available (need runs with different worker counts)")
            return
        
        print("\n" + "="*80)
        print("SPEEDUP ANALYSIS")
        print("="*80)
        print(f"{'Specification':<30} {'Workers':>8} {'Time(s)':>10} {'Speedup':>10} {'Efficiency':>10}")
        print("-"*80)
        
        current_spec = None
        for r in speedup_data:
            spec_name = Path(r['spec_file']).stem
            if spec_name != current_spec:
                if current_spec is not None:
                    print("-"*80)
                current_spec = spec_name
            
            print(f"{spec_name:<30} {r['workers']:>8} {r['time_mean']:>10.1f} "
                  f"{r['speedup']:>10.2f}x {r['efficiency']*100:>9.1f}%")


def main():
    parser = argparse.ArgumentParser(
        description="Analyze TLC benchmark results"
    )
    
    parser.add_argument('results', nargs='+',
                        help='JSON result file(s)')
    parser.add_argument('--latex', action='store_true',
                        help='Output LaTeX table')
    parser.add_argument('--markdown', action='store_true',
                        help='Output Markdown table')
    parser.add_argument('--csv', action='store_true',
                        help='Output CSV')
    parser.add_argument('--speedup', action='store_true',
                        help='Show speedup analysis')
    parser.add_argument('--output', '-o', type=str,
                        help='Output file (otherwise prints to stdout)')
    
    args = parser.parse_args()
    
    # Load all results
    all_results = []
    for filepath in args.results:
        all_results.extend(load_results(filepath))
    
    analyzer = BenchmarkAnalyzer(all_results)
    
    output_lines = []
    
    if args.latex:
        output_lines.append(analyzer.to_latex_table())
    elif args.markdown:
        output_lines.append(analyzer.to_markdown_table())
    elif args.csv:
        output_lines.append(analyzer.to_csv())
    elif args.speedup:
        analyzer.print_speedup_analysis()
    else:
        # Default: print summary
        analyzer.print_summary()
        if any(r.get('workers', 1) > 1 for r in all_results):
            analyzer.print_speedup_analysis()
    
    if output_lines:
        output = "\n\n".join(output_lines)
        
        if args.output:
            with open(args.output, 'w') as f:
                f.write(output)
            print(f"Output written to {args.output}")
        else:
            print(output)


if __name__ == "__main__":
    main()
