#!/usr/bin/env python3
"""Plot all benchmarks found in TLC and Veil result directories.

Reads TLC's csv/tlc-<N>-worker.csv and Veil's
csv/veil-results-rev-<REV>-<N>.csv, discovering thread counts and revisions.
Benchmarks are matched by CSV name (falling back to TLC config/spec names),
sorted by name, and plotted even when only one series has data, with a warning.
Veil runtime includes compilation time, as in plot-model-check-runs.py.

Example:
  python3 scripts/plot-model-check-runs-all.py example-results/tlc example-results/veil -o comparison
"""

import argparse
from pathlib import Path
import re
import runpy
import sys


def discover_series(directory: Path, label: str) -> list[str]:
    """Find per-thread CSV patterns for one results directory."""
    directory = directory.expanduser().resolve()
    if not directory.is_dir():
        sys.exit(f"Error: {label} results directory not found: {directory}")

    filename_re = re.compile(r'tlc-(\d+)-worker\.csv' if label == 'TLC'
                             else r'veil-results-rev-.+-(\d+)\.csv')
    patterns = set()
    for path in (directory / 'csv').glob('*.csv'):
        match = filename_re.fullmatch(path.name)
        if match and path.is_file():
            start, end = match.span(1)
            patterns.add(str(path.with_name(path.name[:start] + '{N}' + path.name[end:])))
    if not patterns:
        sys.exit(f"Error: no {label} per-thread CSV files found in {directory / 'csv'}")
    return [f'{label}:{pattern}' for pattern in sorted(patterns)]


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('tlc_dir', type=Path, help='TLC results directory containing csv/')
    parser.add_argument('veil_dir', type=Path, help='Veil results directory containing csv/')
    parser.add_argument('-o', '--output', type=Path, default=Path('model-check-runs'),
                        help='Output prefix (default: model-check-runs); writes '
                             'PREFIX_time.FORMAT and PREFIX_memory.FORMAT')
    parser.add_argument('--format', choices=['png', 'pdf', 'svg', 'eps'], default='pdf',
                        help='Output file format (default: pdf)')
    parser.add_argument('--grid-cols', type=int, default=4,
                        help='Number of grid columns; rows are added as needed (default: 4)')
    args = parser.parse_args()
    if args.grid_cols < 1:
        parser.error('--grid-cols must be at least 1')

    series = discover_series(args.tlc_dir, 'TLC') + discover_series(args.veil_dir, 'Veil')
    plotter = runpy.run_path(str(Path(__file__).with_name('plot-model-check-runs.py')))
    output = args.output.expanduser()
    output.parent.mkdir(parents=True, exist_ok=True)
    plotter['plot_scaling'](series, None, str(output), output_format=args.format,
                           baseline='TLC', grid_cols=args.grid_cols)


if __name__ == '__main__':
    main()
