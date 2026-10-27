#!/usr/bin/env python3
"""
Compare TLC and Veil runtime and memory usage across worker thread counts.

Draws {prefix}_time.{fmt} and {prefix}_memory.{fmt}. Each figure has one
log-scale subplot per benchmark, plotting wall time (s) or peak memory (MB)
against the number of worker threads for a baseline series (TLC, red squares)
and a compared series (Veil, blue triangles). Veil times include compilation
time.

In each subplot, the solid and dashed arrows mark the thread counts with the
smallest and largest baseline / compared ratio. Both ratios are listed in the
upper right corner, below statistics of the baseline run with the fewest
threads (d = depth, #s = states generated, #ds = distinct states).

Each series is read from CSV files with one row per benchmark and one file per
thread count, selected by a pattern with an {N} placeholder:
  Veil: name, compilation_time_seconds, wall_time_seconds, max_rss_mb, ...
  TLC:  spec_file, config_file, wall_time_seconds, peak_memory_mb, ...
Both formats also have depth, states_generated, and distinct_states columns.

Requires Python 3.9+ with matplotlib and numpy.
"""

import argparse
import csv
import glob
import math
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Optional

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import FuncFormatter, LogLocator, NullLocator


# =============================================================================
# Constants
# =============================================================================

# (line color, marker) of the two series
BASELINE_STYLE = ('#d62728', 's')   # red, squares (TLC)
COMPARED_STYLE = ('#1f77b4', '^')   # blue, triangles (Veil)

# Line styles of the arrows at the smallest and largest ratio
ARROW_STYLES = ['solid', (0, (4, 2))]

# Font size (points) and color of the statistics and ratios in each subplot
CORNER_FONT_SIZE = 5.25
CORNER_COLOR = '#666666'


# =============================================================================
# Generic Utilities
# =============================================================================

def safe_float(val) -> Optional[float]:
    """Safely convert a value to float, returning None on failure."""
    try:
        return float(val) if val else None
    except (ValueError, TypeError):
        return None


def safe_int(val) -> Optional[int]:
    """Safely convert a value to int, returning None on failure."""
    try:
        return int(val) if val else None
    except (ValueError, TypeError):
        return None


def load_csv(filepath: str) -> list[dict]:
    """Load CSV file and return list of dicts."""
    with open(filepath, 'r') as f:
        reader = csv.DictReader(f)
        return list(reader)


# =============================================================================
# Loading Series
# =============================================================================

def discover_series_files(pattern: str) -> list[tuple[int, str]]:
    """
    Find CSV files matching a pattern with {N} placeholder for thread count.
    Returns sorted list of (thread_count, filepath) tuples.
    """
    glob_pattern = pattern.replace('{N}', '*')
    files = glob.glob(glob_pattern)

    # Build regex to extract the integer from the {N} position
    escaped = re.escape(pattern)
    extract_re = re.compile(escaped.replace(re.escape('{N}'), r'(\d+)'))

    result = []
    for f in files:
        m = extract_re.match(f)
        if m:
            result.append((int(m.group(1)), f))
    result.sort(key=lambda x: x[0])
    return result


def extract_experiment_name(row: dict) -> Optional[str]:
    """
    Extract experiment name from a CSV row: the name column for Veil, the
    config file name for TLC.
    """
    if row.get('name'):
        return row['name']
    config = row.get('config_file', '')
    if config:
        # Some TLC tables use MC.cfg for every model; name those rows by their spec.
        if Path(config).name == 'MC.cfg' and row.get('spec_file'):
            return Path(row['spec_file']).stem
        return Path(config).stem
    return None


def extract_memory_mb(row: dict) -> Optional[float]:
    """Extract memory usage in MB from a CSV row (supports Veil and TLC formats)."""
    # Veil: max_rss_mb, TLC: peak_memory_mb
    val = row.get('max_rss_mb') or row.get('peak_memory_mb')
    return safe_float(val)


def wall_plus_compilation(row: dict) -> Optional[float]:
    """Wall time plus compilation time, for rows whose CSV has a compilation_time_seconds
    column (Veil: elaborating the spec and building the checker binary). TLC rows have no
    such column and keep their wall time. A Veil row without a compilation time gives None
    rather than its wall time alone."""
    wall = safe_float(row.get('wall_time_seconds'))
    if wall is None or 'compilation_time_seconds' not in row:
        return wall
    compilation = safe_float(row['compilation_time_seconds'])
    return None if compilation is None else wall + compilation


def load_series_data(series_specs: list[str]) -> tuple[dict, set[int]]:
    """
    Load all series from specs. Returns (series_data, all_thread_counts).
    series_data[label] = {bench_name: {thread_count: row_dict}}

    Sources with the same label are merged; conflicting rows for the same
    benchmark and thread count are rejected.
    """
    series_data = {}
    all_thread_counts = set()

    for spec in series_specs:
        label, separator, pattern = spec.partition(':')
        if not separator or '{N}' not in pattern:
            sys.exit(f"Error: --series must be 'label:pattern' with {{N}} placeholder, got: {spec}")

        file_list = discover_series_files(pattern)
        if not file_list:
            print(f"Warning: No files found for series '{label}' with pattern '{pattern}'",
                  file=sys.stderr)
            continue

        thread_counts = [t for t, _ in file_list]
        all_thread_counts.update(thread_counts)
        print(f"Series '{label}': found {len(file_list)} files, threads: {thread_counts}")

        bench_data = series_data.setdefault(label, {})
        for threads, filepath in file_list:
            for row in load_csv(filepath):
                name = extract_experiment_name(row)
                if name is None:
                    continue
                bench_threads = bench_data.setdefault(name, {})
                if threads in bench_threads and bench_threads[threads] != row:
                    sys.exit(f"Error: conflicting data for series '{label}', "
                             f"benchmark '{name}', threads {threads} in '{filepath}'")
                bench_threads[threads] = row

    return series_data, all_thread_counts


def apply_benchmark_aliases(series_data: dict, aliases: list[str]):
    """Rename benchmarks in every series by exact OLD=NEW mappings."""
    for alias in aliases:
        old, separator, new = alias.partition('=')
        if not separator or not old or not new:
            sys.exit(f"Error: --benchmark-alias must be 'OLD=NEW', got: {alias}")
        found = False
        for label, bench_data in series_data.items():
            if old not in bench_data:
                continue
            if new != old and new in bench_data:
                sys.exit(f"Error: benchmark alias '{alias}' would overwrite '{new}' "
                         f"in series '{label}'")
            bench_data[new] = bench_data.pop(old)
            found = True
        if not found:
            sys.exit(f"Error: benchmark alias source '{old}' not found in any series")


def warn_distinct_states_mismatch(series_data: dict, benchmarks: list[str]):
    """
    Report distinct-state count mismatches across series and thread counts in
    red on stderr. Missing or invalid counts are skipped.
    """
    for bench in benchmarks:
        counts = defaultdict(lambda: defaultdict(list))
        for label, bench_data in series_data.items():
            for threads, row in sorted(bench_data.get(bench, {}).items()):
                count = safe_int(row.get('distinct_states'))
                if count is not None:
                    counts[count][label].append(threads)
        if len(counts) > 1:
            details = []
            for count, series_threads in sorted(counts.items()):
                sources = '; '.join(f'{label} (threads: {", ".join(map(str, threads))})'
                                    for label, threads in series_threads.items())
                details.append(f'  {count:,}: {sources}')
            print(f"\033[31mWarning: distinct_states mismatch for benchmark '{bench}':\n"
                  + '\n'.join(details) + '\033[0m', file=sys.stderr)


# =============================================================================
# Figures
# =============================================================================

def fmt_count(value) -> str:
    """Format a state count compactly, e.g. 1234567 -> '1.2M'."""
    try:
        number = int(value)
    except (ValueError, TypeError):
        return str(value)
    if number >= 1_000_000_000:
        return f'{number / 1_000_000_000:.1f}B'
    if number >= 1_000_000:
        return f'{number / 1_000_000:.1f}M'
    if number >= 1_000:
        return f'{number / 1_000:.1f}K'
    return str(number)


def draw_figure(
    series_data: dict,
    benchmarks: list[str],
    sorted_threads: list[int],
    baseline: str,
    compared: str,
    value_extractor,
    output_path: str,
    output_format: str,
    grid_rows: int,
    grid_cols: int,
):
    """
    Draw a grid with one log-scale subplot per benchmark.

    Solid arrows mark the smallest baseline / compared ratio; dashed arrows
    mark the largest. Ties use the smallest thread count. Matching arrow
    samples and the ratios sit in the upper right corner, below the benchmark
    statistics. Titles drop parameter suffixes such as "-3-3".

    Args:
        value_extractor: callable(row) -> Optional[float] to extract metric value from a CSV row
    """
    fig_width = grid_cols * 1.75
    fig_height = grid_rows * 0.92 + 0.20
    fig = plt.figure(figsize=(fig_width, fig_height))
    # Each benchmark spans two grid columns.
    outer = fig.add_gridspec(grid_rows, 2 * grid_cols, hspace=0.20, wspace=0.34,
                             left=0.25 / fig_width, right=1 - 0.04 / fig_width,
                             bottom=0.16 / fig_height,
                             top=1 - 0.04 / fig_height)

    def positive_value(row):
        value = value_extractor(row) if row else None
        return value if value is not None and np.isfinite(value) and value > 0 else np.nan

    for idx, bench in enumerate(benchmarks):
        row_idx, col_idx = divmod(idx, grid_cols)
        inner = outer[row_idx, 2 * col_idx:2 * col_idx + 2].subgridspec(
            2, 1, hspace=0, height_ratios=[0.12, 0.72])
        ax_header = fig.add_subplot(inner[0])
        ax_header.set_axis_off()
        ax = fig.add_subplot(inner[1])
        plot_height_inches = ax.get_position().height * fig_height
        # One line of corner text, in axes coordinates
        corner_step = (CORNER_FONT_SIZE + 0.5) / (72 * plot_height_inches)
        ax_header.text(0.5, 1, re.sub(r'-[\d].*', '', bench), transform=ax_header.transAxes,
                       fontsize=6.5, fontweight='bold', ha='center', va='top')

        baseline_bench = series_data[baseline].get(bench, {})
        if baseline_bench:
            row = baseline_bench[min(baseline_bench)]
            stats = (f'd={row.get("depth", "")} '
                     f'#s={fmt_count(row.get("states_generated", ""))} '
                     f'#ds={fmt_count(row.get("distinct_states", ""))}')
            ax.text(1, 1, stats, transform=ax.transAxes,
                    fontsize=CORNER_FONT_SIZE, color=CORNER_COLOR, ha='right', va='top',
                    bbox=dict(facecolor='white', edgecolor='none', pad=0.2), zorder=5)

        values_by_label = {}
        for label, (color, marker) in ((baseline, BASELINE_STYLE), (compared, COMPARED_STYLE)):
            bench_threads = series_data[label].get(bench, {})
            values = np.array([positive_value(bench_threads.get(t, {})) for t in sorted_threads])
            values_by_label[label] = values
            valid = np.isfinite(values)
            ax.plot(np.array(sorted_threads)[valid], values[valid],
                    marker=marker, linewidth=1.1, markersize=2.5,
                    color=color, label=label, zorder=3)

        ax.set_yscale('log')
        all_values = np.concatenate(list(values_by_label.values()))
        all_values = all_values[np.isfinite(all_values)]
        if len(all_values):
            # Keep the data range independent of the corner text.
            ax.set_ylim(all_values.min() / 1.2, all_values.max() * 1.2)
        else:
            ax.set_ylim(0.5, 2)
            ax.text(0.5, 0.5, 'No positive data', transform=ax.transAxes,
                    ha='center', va='center', fontsize=6, color='gray')
        ax.yaxis.set_major_locator(LogLocator(base=10, subs=(1, 2, 5)))
        ax.yaxis.set_major_formatter(FuncFormatter(
            lambda value, _: f'{value / 1000:g}k' if value >= 1000 else f'{value:g}'))
        ax.yaxis.set_minor_locator(NullLocator())
        ax.grid(axis='y', color='#E6E6E6', linewidth=0.5)
        ax.tick_params(axis='both', labelsize=5.5, pad=1, width=0.6, length=2.5)
        for side in ('top', 'right'):
            ax.spines[side].set_visible(False)
        for side in ('left', 'bottom'):
            ax.spines[side].set_linewidth(0.6)

        display_threads = set()
        summary_y = 1 - corner_step * 1.5
        ratios = values_by_label[baseline] / values_by_label[compared]
        valid_indices = np.flatnonzero(np.isfinite(ratios) & (ratios > 0))
        if not len(valid_indices):
            ax.text(1, summary_y, 'No paired data', transform=ax.transAxes,
                    ha='right', va='center', fontsize=CORNER_FONT_SIZE, color=CORNER_COLOR)
        else:
            indices = [valid_indices[np.argmin(ratios[valid_indices])],
                       valid_indices[np.argmax(ratios[valid_indices])]]
            for extreme, point_idx in enumerate(indices):
                thread = sorted_threads[point_idx]
                display_threads.add(thread)
                # Separate the two arrow styles when both extrema use one thread.
                offset = (extreme - 0.5) * 0.2 if indices[0] == indices[1] else 0
                arrowprops = dict(arrowstyle='<->', linewidth=0.7, color='black',
                                  linestyle=ARROW_STYLES[extreme], shrinkA=0, shrinkB=0,
                                  mutation_scale=4.5)
                ax.annotate('', xy=(thread + offset, values_by_label[compared][point_idx]),
                            xytext=(thread + offset, values_by_label[baseline][point_idx]),
                            arrowprops=arrowprops, zorder=4)
                # The minimum and maximum are listed on separate lines.
                entry_y = summary_y - extreme * corner_step
                ax.annotate('', xy=(0.8, entry_y), xytext=(0.68, entry_y),
                            xycoords='axes fraction', arrowprops=arrowprops, zorder=5)
                ax.text(1, entry_y, f'{ratios[point_idx]:.1f}×', transform=ax.transAxes,
                        fontsize=CORNER_FONT_SIZE, color=CORNER_COLOR, ha='right', va='center',
                        zorder=5, bbox=dict(facecolor='white', edgecolor='none', pad=0.1))

        # Keep extrema readable when one lies beside an endpoint tick.
        for endpoint in (sorted_threads[0], sorted_threads[-1]):
            if all(thread == endpoint or abs(thread - endpoint) >= 2
                   for thread in display_threads):
                display_threads.add(endpoint)
        ax.set_xticks(sorted(display_threads))
        ax.set_xlim(sorted_threads[0] - 0.6, sorted_threads[-1] + 0.6)

    fig.savefig(output_path, dpi=300, bbox_inches='tight', pad_inches=0.02,
                format=output_format)
    print(f'Saved: {output_path}')
    plt.close(fig)


def plot_scaling(
    series_specs: list[str],
    benchmarks: Optional[list[str]],
    output_prefix: str,
    output_format: str = 'pdf',
    baseline: Optional[str] = None,
    benchmark_aliases: Optional[list[str]] = None,
    grid_cols: int = 4,
):
    """
    Draw the time and memory figures.

    Reports distinct-state count mismatches across series and thread counts
    before drawing.

    Args:
        series_specs: List of "label:pattern" strings; exactly two labels
        benchmarks: Benchmark names in grid order, or None to plot all names sorted
        output_prefix: Output file prefix
        output_format: Output file format (png, pdf, svg, eps)
        baseline: Label of the baseline series (default: first series)
        benchmark_aliases: Exact OLD=NEW benchmark name mappings applied to each series
        grid_cols: Number of grid columns; rows are added as needed
    """
    series_data, all_thread_counts = load_series_data(series_specs)
    labels = list(series_data.keys())
    if len(labels) != 2:
        sys.exit(f"Error: expected two series (a baseline and a compared series), got: {labels}")
    if baseline is None:
        baseline = labels[0]
    if baseline not in series_data:
        sys.exit(f"Error: baseline '{baseline}' not found in series {labels}")
    compared = labels[1] if baseline == labels[0] else labels[0]
    print(f"Baseline series: '{baseline}'")

    apply_benchmark_aliases(series_data, benchmark_aliases or [])

    # Validate benchmarks
    all_bench_names = set()
    for bench_data in series_data.values():
        all_bench_names.update(bench_data.keys())
    if benchmarks is None:
        benchmarks = sorted(all_bench_names)
    valid_benchmarks = []
    for b in benchmarks:
        if b in all_bench_names:
            valid_benchmarks.append(b)
            for label, bench_data in series_data.items():
                if b not in bench_data:
                    print(f"Warning: benchmark '{b}' not found in series '{label}'",
                          file=sys.stderr)
        else:
            print(f"Warning: benchmark '{b}' not found in any series",
                  file=sys.stderr)
    if not valid_benchmarks:
        sys.exit("Error: No valid benchmarks.")

    warn_distinct_states_mismatch(series_data, valid_benchmarks)

    grid_rows = math.ceil(len(valid_benchmarks) / grid_cols)
    print(f"Benchmarks ({len(valid_benchmarks)}): {valid_benchmarks}")
    print(f"Grid: {grid_rows} rows x {grid_cols} cols "
          f"({grid_rows * grid_cols - len(valid_benchmarks)} empty cell(s))")

    compiled_labels = [label for label in labels
                       if any('compilation_time_seconds' in row
                              for rows in series_data[label].values() for row in rows.values())]
    if not compiled_labels:
        print("Warning: no series has a compilation_time_seconds column; "
              "the time figure shows wall time only", file=sys.stderr)
    else:
        print(f"Adding compilation time to: {compiled_labels}")
    missing = [f'{label}/{bench}/{threads}'
               for label in compiled_labels for bench in valid_benchmarks
               for threads, row in sorted(series_data[label].get(bench, {}).items())
               if safe_float(row.get('wall_time_seconds')) is not None
               and safe_float(row.get('compilation_time_seconds')) is None]
    if missing:
        print(f"Warning: {len(missing)} point(s) have a wall time but no compilation time "
              f"and are left out of the time figure: {', '.join(missing)}", file=sys.stderr)

    shared = dict(
        series_data=series_data,
        benchmarks=valid_benchmarks,
        sorted_threads=sorted(all_thread_counts),
        baseline=baseline,
        compared=compared,
        output_format=output_format,
        grid_rows=grid_rows,
        grid_cols=grid_cols,
    )

    # Time figure
    draw_figure(
        **shared,
        value_extractor=wall_plus_compilation,
        output_path=f"{output_prefix}_time.{output_format}",
    )

    # Memory figure
    draw_figure(
        **shared,
        value_extractor=extract_memory_mb,
        output_path=f"{output_prefix}_memory.{output_format}",
    )


# =============================================================================
# CLI Entry Point
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description='Compare runtime and memory usage against '
                    'worker threads, TLC vs. Veil',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Example with a fictional Counter benchmark and 1- and 2-thread CSV files:
  python scripts/plot-model-check-runs.py \\
    --series "TLC:example-results/tlc-{N}.csv" \\
    --series "Veil:example-results/veil-{N}.csv" \\
    --benchmarks Counter --grid-cols 1 -o counter
        """
    )
    parser.add_argument('--series', action='append', required=True, metavar='LABEL:PATTERN',
                        help='Series source, where {N} in PATTERN is the thread count. '
                             'Repeat for each source; sources with the same LABEL are merged, '
                             'and conflicting rows for the same benchmark and thread count are '
                             'rejected. Exactly two labels are expected.')
    parser.add_argument('--baseline', default=None,
                        help='Label of the baseline series for the ratios (default: first series)')
    parser.add_argument('--benchmarks', nargs='+', required=True,
                        help='Benchmark names to plot, in grid order (e.g., Counter)')
    parser.add_argument('--benchmark-alias', action='append', default=None, metavar='OLD=NEW',
                        help='Exact OLD=NEW benchmark name mapping applied to each series before '
                             'selection; repeat for multiple names. Existing names cannot be overwritten.')
    parser.add_argument('-o', '--output', required=True,
                        help='Output file prefix (writes PREFIX_time.FORMAT and PREFIX_memory.FORMAT)')
    parser.add_argument('--format', choices=['png', 'pdf', 'svg', 'eps'], default='pdf',
                        help='Output file format (default: pdf)')
    parser.add_argument('--grid-cols', type=int, default=4,
                        help='Number of grid columns; rows are added as needed (default: 4)')

    args = parser.parse_args()
    if args.grid_cols < 1:
        parser.error('--grid-cols must be at least 1')

    plot_scaling(
        args.series,
        args.benchmarks,
        args.output,
        output_format=args.format,
        baseline=args.baseline,
        benchmark_aliases=args.benchmark_alias,
        grid_cols=args.grid_cols,
    )


if __name__ == '__main__':
    main()
