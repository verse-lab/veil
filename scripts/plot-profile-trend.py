"""
Plot profiling time trends across multiple profile runs.

Usage:
    ./scripts/plot-profile-trend.py <file1> <file2> ...
    ./scripts/plot-profile-trend.py profiles/nopaxos-old.txt profiles/nopaxos-new.txt profiles/nopaxos-new2.txt
    ./scripts/plot-profile-trend.py profiles/test-ivy/timing.txt profiles/test-ivy-new/timing.txt

Labels are derived automatically from file/directory names. You can override
with --labels:
    ./scripts/plot-profile-trend.py f1.txt f2.txt --labels old new

Options:
    --top N             Show top N functions by max total time (default: 20)
    --metric METRIC     "total" or "self" (default: total)
    --output FILE       Save plot to file (format inferred from extension: .png, .pdf, .svg, ...)
    --group PATTERN     Aggregate all functions matching PATTERN into one bar (can be repeated).
                        E.g., --group discharger --group "smt."
    --exclude PATTERN   Exclude functions matching pattern (can be repeated)
    --filter PATTERN    Only include functions matching pattern (can be repeated)
    --title TITLE       Custom plot title
    --labels L1 L2 ...  Custom labels for each input file
"""

import argparse
import os
import re
import sys
from collections import defaultdict

import matplotlib.pyplot as plt
import numpy as np


def parse_profile_output(path: str) -> dict:
    """Parse a profile output file (from parse-profile.py).

    Returns dict: func_name -> {"self_time": ms, "total_time": ms, "count": n}
    """
    stats = {}
    in_table = False
    with open(path, 'r') as f:
        for line in f:
            line = line.rstrip()
            # Detect table header
            if line.startswith('Function') and 'Self (ms)' in line:
                in_table = True
                continue
            if in_table and line.startswith('---'):
                continue
            if in_table and line:
                # Parse table row: name followed by 3 numeric columns
                # The name can contain spaces and be truncated with "..."
                match = re.match(
                    r'^(.+?)\s{2,}(\d+\.?\d*)\s+(\d+\.?\d*)\s+(\d+)\s*$', line
                )
                if match:
                    name = match.group(1).strip()
                    self_time = float(match.group(2))
                    total_time = float(match.group(3))
                    count = int(match.group(4))
                    stats[name] = {
                        "self_time": self_time,
                        "total_time": total_time,
                        "count": count,
                    }
                else:
                    # End of table
                    if in_table and not line.startswith(' '):
                        in_table = False
    return stats


def aggregate_by_patterns(stats: dict, patterns: list) -> dict:
    """Aggregate functions matching each pattern into a single entry.

    Each pattern is matched as a substring. Functions matching a pattern are
    merged into a group named after the pattern. Functions not matching any
    pattern are kept as-is. Patterns are checked in order; the first match wins.
    """
    groups = defaultdict(lambda: {"self_time": 0, "total_time": 0, "count": 0})
    for name, data in stats.items():
        matched = False
        for pattern in patterns:
            if pattern in name:
                label = f"{pattern}*"
                groups[label]["self_time"] += data["self_time"]
                groups[label]["total_time"] += data["total_time"]
                groups[label]["count"] += data["count"]
                matched = True
                break
        if not matched:
            groups[name] = {
                "self_time": groups[name]["self_time"] + data["self_time"],
                "total_time": groups[name]["total_time"] + data["total_time"],
                "count": groups[name]["count"] + data["count"],
            }
    return dict(groups)


def derive_label(path: str) -> str:
    """Derive a short label from a file path.

    Examples:
        profiles/nopaxos-old.txt        -> nopaxos-old
        profiles/test-ivy/timing.txt    -> test-ivy
        profiles/test-ivy-new/timing.txt -> test-ivy-new
        foo.txt                         -> foo
    """
    basename = os.path.basename(path)
    name_no_ext = os.path.splitext(basename)[0]
    # If the filename is generic (timing, summary, etc.), use the parent dir name
    if name_no_ext in ('timing', 'summary'):
        parent = os.path.basename(os.path.dirname(path))
        return parent if parent else name_no_ext
    return name_no_ext


def main():
    parser = argparse.ArgumentParser(
        description='Plot profiling time trends across multiple runs'
    )
    parser.add_argument('inputs', nargs='+',
                        help='Profile output files (e.g., profiles/nopaxos-old.txt)')
    parser.add_argument('--labels', nargs='+', default=None,
                        help='Custom labels for each input file')
    parser.add_argument('--top', type=int, default=20,
                        help='Show top N functions (default: 20)')
    parser.add_argument('--metric', choices=['total', 'self'], default='total',
                        help='Which metric to plot (default: total)')
    parser.add_argument('--output', '-o', default=None,
                        help='Save plot to file (format from extension: .png, .pdf, .svg, ...)')
    parser.add_argument('--group', '-g', action='append', default=[],
                        help='Aggregate functions matching PATTERN into one bar (can be repeated)')
    parser.add_argument('--exclude', '-e', action='append', default=[],
                        help='Exclude functions matching pattern')
    parser.add_argument('--filter', '-f', action='append', default=[],
                        help='Only include functions matching pattern')
    parser.add_argument('--title', default=None, help='Custom title')
    args = parser.parse_args()

    if args.labels and len(args.labels) != len(args.inputs):
        print(f"Error: --labels count ({len(args.labels)}) must match "
              f"input count ({len(args.inputs)})", file=sys.stderr)
        sys.exit(1)

    # Derive labels from file paths if not provided
    labels = args.labels or [derive_label(p) for p in args.inputs]

    # Parse inputs
    all_stats = []
    for path in args.inputs:
        stats = parse_profile_output(path)
        if args.group:
            stats = aggregate_by_patterns(stats, args.group)
        all_stats.append(stats)

    metric_key = f"{args.metric}_time"

    # Collect all function names
    all_funcs = set()
    for stats in all_stats:
        all_funcs.update(stats.keys())

    # Apply filters
    if args.filter:
        all_funcs = {f for f in all_funcs
                     if any(p in f for p in args.filter)}
    if args.exclude:
        all_funcs = {f for f in all_funcs
                     if not any(p in f for p in args.exclude)}

    # Rank by max value across runs
    func_max = {}
    for func in all_funcs:
        func_max[func] = max(
            stats.get(func, {}).get(metric_key, 0) for stats in all_stats
        )

    top_funcs = sorted(func_max.keys(), key=lambda f: func_max[f], reverse=True)
    top_funcs = top_funcs[:args.top]

    # Build data matrix
    data = np.zeros((len(top_funcs), len(labels)))
    for j, stats in enumerate(all_stats):
        for i, func in enumerate(top_funcs):
            data[i, j] = stats.get(func, {}).get(metric_key, 0)

    # Convert to seconds for readability
    data_sec = data / 1000.0

    # Plot
    fig, ax = plt.subplots(figsize=(14, max(6, len(top_funcs) * 0.4)))

    x = np.arange(len(top_funcs))
    bar_width = 0.8 / len(labels)
    cmap = plt.colormaps['Set2']
    colors = cmap(np.linspace(0, 1, max(len(labels), 3)))

    row_height = 0.4 + max(0, len(labels) - 3) * 0.1
    fig.set_size_inches(14, max(6, len(top_funcs) * row_height))
    label_fontsize = max(5, 7 - max(0, len(labels) - 4) * 0.5)

    for j, label in enumerate(labels):
        offset = (j - len(labels) / 2 + 0.5) * bar_width
        bars = ax.barh(x + offset, data_sec[:, j], bar_width * 0.9,
                       label=label, color=colors[j])
        # Add value labels on bars
        for bar, val in zip(bars, data_sec[:, j]):
            if val > 0:
                ax.text(bar.get_width() + 0.1, bar.get_y() + bar.get_height() / 2,
                        f'{val:.1f}', va='center', fontsize=label_fontsize, color='#333')
            else:
                ax.text(0.1, bar.get_y() + bar.get_height() / 2,
                        '0.0', va='center', fontsize=label_fontsize, color='#999')

    ax.set_yticks(x)
    # Shorten long labels
    short_labels = []
    for f in top_funcs:
        if len(f) > 50:
            short_labels.append(f[:47] + '...')
        else:
            short_labels.append(f)
    ax.set_yticklabels(short_labels, fontsize=8)
    ax.invert_yaxis()
    ax.set_xlabel(f'{args.metric.capitalize()} time (seconds)')
    title = args.title or f'Profile Comparison — {args.metric.capitalize()} Time'
    ax.set_title(title)
    ax.legend(loc='lower right')
    ax.grid(axis='x', alpha=0.3)

    plt.tight_layout()

    if args.output:
        plt.savefig(args.output, dpi=150, bbox_inches='tight')
        print(f"Saved to {args.output}")
    else:
        plt.show()


if __name__ == '__main__':
    main()
