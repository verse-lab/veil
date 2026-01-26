#!/usr/bin/env python3
"""
TLC Benchmark Results Visualization

This script generates plots from TLC benchmark results, including:
- Progress over time (states vs time)
- Memory consumption over time
- Comparison charts across configurations
- Summary statistics

Usage:
    python plot_results.py benchmark_results_TIMESTAMP.json
    python plot_results.py --progress benchmark_results_TIMESTAMP_progress.json
    python plot_results.py --compare results1.json results2.json
"""

import argparse
import json
import sys
from pathlib import Path
from typing import List, Dict, Any, Optional

try:
    import matplotlib.pyplot as plt
    import matplotlib.ticker as ticker
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False
    print("Error: matplotlib required for plotting.")
    print("Install with: pip install matplotlib")

try:
    import numpy as np
    NUMPY_AVAILABLE = True
except ImportError:
    NUMPY_AVAILABLE = False


def load_json(filepath: str) -> Any:
    """Load JSON file."""
    with open(filepath, 'r') as f:
        return json.load(f)


def format_time(seconds: float) -> str:
    """Format seconds into human-readable string."""
    if seconds < 60:
        return f"{seconds:.1f}s"
    elif seconds < 3600:
        return f"{seconds/60:.1f}m"
    else:
        return f"{seconds/3600:.1f}h"


def format_states(states: int) -> str:
    """Format state count with K/M suffix."""
    if states < 1000:
        return str(states)
    elif states < 1_000_000:
        return f"{states/1000:.1f}K"
    else:
        return f"{states/1_000_000:.2f}M"


class BenchmarkPlotter:
    """Generate plots from benchmark results."""
    
    def __init__(self, output_dir: str = "plots"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        # Set style
        plt.style.use('seaborn-v0_8-whitegrid' if 'seaborn-v0_8-whitegrid' in plt.style.available 
                      else 'seaborn-whitegrid' if 'seaborn-whitegrid' in plt.style.available
                      else 'ggplot')
        
        # Color palette
        self.colors = plt.cm.tab10.colors
    
    def plot_progress(self, 
                      results: List[Dict],
                      title: str = "TLC Model Checking Progress",
                      save_name: str = "progress") -> str:
        """
        Plot state space exploration progress over time.
        
        Creates a multi-panel figure showing:
        - States generated over time
        - Distinct states over time
        - States in queue over time
        """
        fig, axes = plt.subplots(2, 2, figsize=(14, 10))
        fig.suptitle(title, fontsize=14, fontweight='bold')
        
        for idx, result in enumerate(results):
            progress = result.get('progress_points', [])
            if not progress:
                continue
            
            color = self.colors[idx % len(self.colors)]
            label = f"{Path(result['spec_file']).stem} (w={result.get('workers', 1)})"
            
            times = [p['timestamp'] for p in progress]
            states_gen = [p['states_generated'] for p in progress]
            states_dist = [p['distinct_states'] for p in progress]
            states_queue = [p['states_in_queue'] for p in progress]
            memory = [p.get('memory_mb', 0) for p in progress]
            
            # States generated
            axes[0, 0].plot(times, states_gen, color=color, label=label, linewidth=2)
            axes[0, 0].set_xlabel('Time (seconds)')
            axes[0, 0].set_ylabel('States Generated')
            axes[0, 0].set_title('Total States Generated')
            axes[0, 0].legend(loc='upper left', fontsize=8)
            
            # Distinct states
            axes[0, 1].plot(times, states_dist, color=color, label=label, linewidth=2)
            axes[0, 1].set_xlabel('Time (seconds)')
            axes[0, 1].set_ylabel('Distinct States')
            axes[0, 1].set_title('Distinct States Found')
            axes[0, 1].legend(loc='upper left', fontsize=8)
            
            # States in queue
            axes[1, 0].plot(times, states_queue, color=color, label=label, linewidth=2)
            axes[1, 0].set_xlabel('Time (seconds)')
            axes[1, 0].set_ylabel('States in Queue')
            axes[1, 0].set_title('BFS Queue Size')
            axes[1, 0].legend(loc='upper left', fontsize=8)
            
            # Memory (if available)
            if any(m > 0 for m in memory):
                axes[1, 1].plot(times, memory, color=color, label=label, linewidth=2)
        
        axes[1, 1].set_xlabel('Time (seconds)')
        axes[1, 1].set_ylabel('Memory (MB)')
        axes[1, 1].set_title('Memory Consumption')
        axes[1, 1].legend(loc='upper left', fontsize=8)
        
        # Format y-axis with K/M suffixes
        for ax in [axes[0, 0], axes[0, 1], axes[1, 0]]:
            ax.yaxis.set_major_formatter(
                ticker.FuncFormatter(lambda x, p: format_states(int(x)))
            )
        
        plt.tight_layout()
        
        filepath = self.output_dir / f"{save_name}.png"
        plt.savefig(filepath, dpi=150, bbox_inches='tight')
        plt.savefig(self.output_dir / f"{save_name}.pdf", bbox_inches='tight')
        plt.close()
        
        return str(filepath)
    
    def plot_throughput(self,
                        results: List[Dict],
                        title: str = "State Exploration Throughput",
                        save_name: str = "throughput") -> str:
        """Plot states per second over time."""
        fig, ax = plt.subplots(figsize=(12, 6))
        
        for idx, result in enumerate(results):
            progress = result.get('progress_points', [])
            if len(progress) < 2:
                continue
            
            color = self.colors[idx % len(self.colors)]
            label = f"{Path(result['spec_file']).stem} (w={result.get('workers', 1)})"
            
            # Calculate throughput (states/second) between progress points
            times = []
            throughputs = []
            
            for i in range(1, len(progress)):
                dt = progress[i]['timestamp'] - progress[i-1]['timestamp']
                if dt > 0:
                    ds = progress[i]['states_generated'] - progress[i-1]['states_generated']
                    throughput = ds / dt
                    times.append(progress[i]['timestamp'])
                    throughputs.append(throughput)
            
            if times:
                ax.plot(times, throughputs, color=color, label=label, 
                       linewidth=2, alpha=0.8)
        
        ax.set_xlabel('Time (seconds)', fontsize=12)
        ax.set_ylabel('States per Second', fontsize=12)
        ax.set_title(title, fontsize=14, fontweight='bold')
        ax.legend(loc='upper right')
        ax.yaxis.set_major_formatter(
            ticker.FuncFormatter(lambda x, p: format_states(int(x)))
        )
        
        plt.tight_layout()
        
        filepath = self.output_dir / f"{save_name}.png"
        plt.savefig(filepath, dpi=150, bbox_inches='tight')
        plt.close()
        
        return str(filepath)
    
    def plot_comparison_bar(self,
                            results: List[Dict],
                            metric: str = 'wall_time_seconds',
                            title: str = "Benchmark Comparison",
                            ylabel: str = "Time (seconds)",
                            save_name: str = "comparison") -> str:
        """Create bar chart comparing results across configurations."""
        fig, ax = plt.subplots(figsize=(12, 6))
        
        # Group by spec and config
        labels = []
        values = []
        colors = []
        
        for idx, result in enumerate(results):
            spec = Path(result['spec_file']).stem
            cfg = Path(result.get('config_file', 'default')).stem
            workers = result.get('workers', 1)
            
            label = f"{spec}\n{cfg}\nw={workers}"
            labels.append(label)
            values.append(result.get(metric, 0))
            colors.append(self.colors[idx % len(self.colors)])
        
        x = range(len(labels))
        bars = ax.bar(x, values, color=colors, edgecolor='black', linewidth=0.5)
        
        ax.set_xticks(x)
        ax.set_xticklabels(labels, fontsize=9)
        ax.set_ylabel(ylabel, fontsize=12)
        ax.set_title(title, fontsize=14, fontweight='bold')
        
        # Add value labels on bars
        for bar, val in zip(bars, values):
            height = bar.get_height()
            if metric == 'wall_time_seconds':
                label = format_time(val)
            elif 'states' in metric:
                label = format_states(int(val))
            elif 'memory' in metric:
                label = f"{val:.0f}MB"
            else:
                label = f"{val:.2f}"
            
            ax.annotate(label,
                       xy=(bar.get_x() + bar.get_width() / 2, height),
                       xytext=(0, 3),
                       textcoords="offset points",
                       ha='center', va='bottom', fontsize=9)
        
        plt.tight_layout()
        
        filepath = self.output_dir / f"{save_name}_{metric}.png"
        plt.savefig(filepath, dpi=150, bbox_inches='tight')
        plt.close()
        
        return str(filepath)
    
    def plot_workers_scaling(self,
                             results: List[Dict],
                             title: str = "Worker Scaling Analysis",
                             save_name: str = "scaling") -> str:
        """Plot how performance scales with number of workers."""
        fig, axes = plt.subplots(1, 2, figsize=(14, 5))
        
        # Group results by spec
        specs = {}
        for result in results:
            spec = Path(result['spec_file']).stem
            if spec not in specs:
                specs[spec] = []
            specs[spec].append(result)
        
        for idx, (spec, spec_results) in enumerate(specs.items()):
            color = self.colors[idx % len(self.colors)]
            
            # Sort by workers
            spec_results.sort(key=lambda x: x.get('workers', 1))
            
            workers = [r.get('workers', 1) for r in spec_results]
            times = [r.get('wall_time_seconds', 0) for r in spec_results]
            
            # Time vs workers
            axes[0].plot(workers, times, 'o-', color=color, label=spec, 
                        linewidth=2, markersize=8)
            
            # Speedup vs workers
            if times and times[0] > 0:
                speedups = [times[0] / t if t > 0 else 0 for t in times]
                axes[1].plot(workers, speedups, 'o-', color=color, label=spec,
                            linewidth=2, markersize=8)
        
        # Ideal speedup line
        max_workers = max(r.get('workers', 1) for r in results)
        ideal_workers = list(range(1, max_workers + 1))
        axes[1].plot(ideal_workers, ideal_workers, '--', color='gray', 
                    label='Ideal', alpha=0.5)
        
        axes[0].set_xlabel('Number of Workers', fontsize=12)
        axes[0].set_ylabel('Time (seconds)', fontsize=12)
        axes[0].set_title('Execution Time vs Workers', fontsize=12)
        axes[0].legend()
        
        axes[1].set_xlabel('Number of Workers', fontsize=12)
        axes[1].set_ylabel('Speedup', fontsize=12)
        axes[1].set_title('Speedup vs Workers', fontsize=12)
        axes[1].legend()
        
        plt.suptitle(title, fontsize=14, fontweight='bold')
        plt.tight_layout()
        
        filepath = self.output_dir / f"{save_name}.png"
        plt.savefig(filepath, dpi=150, bbox_inches='tight')
        plt.close()
        
        return str(filepath)
    
    def plot_summary_dashboard(self,
                               results: List[Dict],
                               title: str = "Benchmark Summary Dashboard",
                               save_name: str = "dashboard") -> str:
        """Create a comprehensive summary dashboard."""
        fig = plt.figure(figsize=(16, 12))
        
        # Layout: 2x2 + bottom bar
        gs = fig.add_gridspec(3, 2, height_ratios=[1, 1, 0.8])
        
        ax1 = fig.add_subplot(gs[0, 0])  # Time comparison
        ax2 = fig.add_subplot(gs[0, 1])  # States comparison
        ax3 = fig.add_subplot(gs[1, 0])  # Memory comparison
        ax4 = fig.add_subplot(gs[1, 1])  # Success rate pie
        ax5 = fig.add_subplot(gs[2, :])  # Summary table
        
        labels = []
        times = []
        states = []
        memory = []
        success = 0
        timeout = 0
        error = 0
        
        for result in results:
            spec = Path(result['spec_file']).stem
            workers = result.get('workers', 1)
            labels.append(f"{spec}\nw={workers}")
            times.append(result.get('wall_time_seconds', 0))
            states.append(result.get('distinct_states', 0))
            memory.append(result.get('peak_memory_mb', 0))
            
            if result.get('success'):
                success += 1
            elif result.get('timeout'):
                timeout += 1
            else:
                error += 1
        
        x = range(len(labels))
        
        # Time bar chart
        ax1.bar(x, times, color=self.colors[0], edgecolor='black')
        ax1.set_xticks(x)
        ax1.set_xticklabels(labels, fontsize=8, rotation=45, ha='right')
        ax1.set_ylabel('Time (seconds)')
        ax1.set_title('Execution Time')
        
        # States bar chart
        ax2.bar(x, states, color=self.colors[1], edgecolor='black')
        ax2.set_xticks(x)
        ax2.set_xticklabels(labels, fontsize=8, rotation=45, ha='right')
        ax2.set_ylabel('Distinct States')
        ax2.set_title('State Space Size')
        ax2.yaxis.set_major_formatter(
            ticker.FuncFormatter(lambda x, p: format_states(int(x)))
        )
        
        # Memory bar chart
        ax3.bar(x, memory, color=self.colors[2], edgecolor='black')
        ax3.set_xticks(x)
        ax3.set_xticklabels(labels, fontsize=8, rotation=45, ha='right')
        ax3.set_ylabel('Peak Memory (MB)')
        ax3.set_title('Memory Usage')
        
        # Success rate pie chart
        pie_data = []
        pie_labels = []
        pie_colors = []
        if success > 0:
            pie_data.append(success)
            pie_labels.append(f'Success ({success})')
            pie_colors.append('#2ecc71')
        if timeout > 0:
            pie_data.append(timeout)
            pie_labels.append(f'Timeout ({timeout})')
            pie_colors.append('#f39c12')
        if error > 0:
            pie_data.append(error)
            pie_labels.append(f'Error ({error})')
            pie_colors.append('#e74c3c')
        
        if pie_data:
            ax4.pie(pie_data, labels=pie_labels, colors=pie_colors, autopct='%1.0f%%',
                   startangle=90)
        ax4.set_title('Completion Status')
        
        # Summary table
        ax5.axis('off')
        
        table_data = []
        headers = ['Spec', 'Workers', 'Time', 'States', 'Memory', 'Status']
        for result in results:
            status = '✓' if result.get('success') else ('⏱' if result.get('timeout') else '✗')
            table_data.append([
                Path(result['spec_file']).stem,
                result.get('workers', 1),
                format_time(result.get('wall_time_seconds', 0)),
                format_states(result.get('distinct_states', 0)),
                f"{result.get('peak_memory_mb', 0):.0f}MB",
                status
            ])
        
        table = ax5.table(cellText=table_data, colLabels=headers,
                         loc='center', cellLoc='center')
        table.auto_set_font_size(False)
        table.set_fontsize(9)
        table.scale(1.2, 1.5)
        
        # Color header
        for i in range(len(headers)):
            table[(0, i)].set_facecolor('#3498db')
            table[(0, i)].set_text_props(color='white', fontweight='bold')
        
        plt.suptitle(title, fontsize=16, fontweight='bold', y=0.98)
        plt.tight_layout()
        
        filepath = self.output_dir / f"{save_name}.png"
        plt.savefig(filepath, dpi=150, bbox_inches='tight')
        plt.close()
        
        return str(filepath)
    
    def generate_all_plots(self, results: List[Dict], prefix: str = "benchmark"):
        """Generate all available plots."""
        plots = []
        
        print("Generating plots...")
        
        # Progress plots (if progress data available)
        has_progress = any(r.get('progress_points') for r in results)
        if has_progress:
            print("  - Progress over time...")
            plots.append(self.plot_progress(results, save_name=f"{prefix}_progress"))
            print("  - Throughput...")
            plots.append(self.plot_throughput(results, save_name=f"{prefix}_throughput"))
        
        # Comparison plots
        print("  - Time comparison...")
        plots.append(self.plot_comparison_bar(results, 'wall_time_seconds', 
                     'Execution Time Comparison', 'Time (seconds)',
                     save_name=f"{prefix}_time"))
        
        print("  - States comparison...")
        plots.append(self.plot_comparison_bar(results, 'distinct_states',
                     'State Space Size Comparison', 'Distinct States',
                     save_name=f"{prefix}_states"))
        
        print("  - Memory comparison...")
        plots.append(self.plot_comparison_bar(results, 'peak_memory_mb',
                     'Memory Usage Comparison', 'Peak Memory (MB)',
                     save_name=f"{prefix}_memory"))
        
        # Scaling analysis (if multiple worker counts)
        worker_counts = set(r.get('workers', 1) for r in results)
        if len(worker_counts) > 1:
            print("  - Scaling analysis...")
            plots.append(self.plot_workers_scaling(results, save_name=f"{prefix}_scaling"))
        
        # Summary dashboard
        print("  - Summary dashboard...")
        plots.append(self.plot_summary_dashboard(results, save_name=f"{prefix}_dashboard"))
        
        print(f"\nGenerated {len(plots)} plots in {self.output_dir}/")
        return plots


def main():
    if not MATPLOTLIB_AVAILABLE:
        print("matplotlib is required. Install with: pip install matplotlib")
        sys.exit(1)
    
    parser = argparse.ArgumentParser(
        description="Generate plots from TLC benchmark results"
    )
    
    parser.add_argument('results', nargs='+',
                        help='JSON result file(s) from tlc_benchmark.py')
    parser.add_argument('--output', '-o', type=str, default='plots',
                        help='Output directory for plots (default: plots)')
    parser.add_argument('--prefix', '-p', type=str, default='benchmark',
                        help='Prefix for output files (default: benchmark)')
    parser.add_argument('--progress-only', action='store_true',
                        help='Generate only progress plots')
    parser.add_argument('--comparison-only', action='store_true',
                        help='Generate only comparison plots')
    
    args = parser.parse_args()
    
    # Load all result files
    all_results = []
    for filepath in args.results:
        print(f"Loading {filepath}...")
        data = load_json(filepath)
        if isinstance(data, list):
            all_results.extend(data)
        else:
            all_results.append(data)
    
    print(f"Loaded {len(all_results)} benchmark results")
    
    # Generate plots
    plotter = BenchmarkPlotter(output_dir=args.output)
    
    if args.progress_only:
        plotter.plot_progress(all_results, save_name=f"{args.prefix}_progress")
        plotter.plot_throughput(all_results, save_name=f"{args.prefix}_throughput")
    elif args.comparison_only:
        plotter.plot_comparison_bar(all_results, 'wall_time_seconds',
                                   save_name=f"{args.prefix}_time")
        plotter.plot_comparison_bar(all_results, 'distinct_states',
                                   save_name=f"{args.prefix}_states")
        plotter.plot_comparison_bar(all_results, 'peak_memory_mb',
                                   save_name=f"{args.prefix}_memory")
    else:
        plotter.generate_all_plots(all_results, prefix=args.prefix)


if __name__ == "__main__":
    main()
