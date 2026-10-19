#!/usr/bin/env python3
"""Replay exact depth-N queries emitted by the finalized preprocessing benchmark."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

from make_solver_checks import MODELS


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--queries', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--depths', type=int, nargs='+', default=[4, 8])
    parser.add_argument('--solver-timeout', type=int, default=10)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    manifest = []
    for name, _, _ in MODELS:
        for depth in args.depths:
            for mode, source_mode in [('old', 'current'), ('early', 'early')]:
                source = args.queries.resolve() / f'{name}_{source_mode}_{depth}_1.smt2'
                target = output / f'{name}_{mode}_{depth}.smt2'
                row = dict(model=name, depth=depth, mode=mode, source=str(source),
                           target=str(target), exists=source.exists())
                if source.exists():
                    shutil.copyfile(source, target)
                    row['sha256'] = hashlib.sha256(target.read_bytes()).hexdigest()
                elif target.exists():
                    # Avoid replaying stale queries if the caller reuses an output directory.
                    target.unlink()
                manifest.append(row)
    (output / 'models.json').write_text(json.dumps(MODELS, indent=2) + '\n')
    (output / 'query-provenance.json').write_text(json.dumps(manifest, indent=2) + '\n')
    command = [sys.executable, str(Path(__file__).with_name('run_solver_checks.py')),
               '--repo', str(args.repo.resolve()), '--output', str(output),
               '--replay-only', '--depths', *map(str, args.depths),
               '--solver-timeout', str(args.solver_timeout)]
    raise SystemExit(subprocess.run(command).returncode)


if __name__ == '__main__':
    main()
