#!/usr/bin/env python3
"""Rebuild production widgets and check their committed JavaScript and dependency trace.

Run after fetching Lake dependencies. Rebuild in a temporary project without old
dist/js files, so deleted modules and orphaned bundles cannot survive the check.
The checkout is never modified. Trace logs and input paths are machine-specific;
only its dependency hash needs to match.
"""

import json
from pathlib import Path
import subprocess
import sys
import shutil
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    bundle_dir = root / 'widget' / 'js'
    trace_file = bundle_dir / 'lake.trace'
    original_trace = trace_file.read_bytes()
    original_js = {p.name: p.read_bytes() for p in bundle_dir.glob('*.js')}
    with tempfile.TemporaryDirectory(prefix='veil-widget-rebuild-') as directory:
        project = Path(directory)
        for name in ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain']:
            shutil.copyfile(root / name, project / name)
        shutil.copytree(root / 'widget', project / 'widget', ignore=shutil.ignore_patterns(
            'node_modules', 'dist', 'js', '*.hash', '*.trace'))
        (project / '.lake').mkdir()
        (project / '.lake' / 'packages').symlink_to(root / '.lake' / 'packages',
                                                  target_is_directory=True)
        subprocess.run(['lake', 'build', 'widgetJsAll'], cwd=project, check=True)
        rebuilt_dir = project / 'widget' / 'js'
        rebuilt_js = {p.name: p.read_bytes() for p in rebuilt_dir.glob('*.js')}
        if original_js != rebuilt_js:
            sys.exit('Widget bundles differ. Delete widget/js/lake.trace, run lake build, and commit widget/js/.')
        if json.loads(original_trace)['depHash'] != json.loads((rebuilt_dir / 'lake.trace').read_bytes())['depHash']:
            sys.exit('Widget trace is stale. Run lake build widgetJsAll and commit widget/js/.')
    print('Committed widget JavaScript and dependency trace are up to date.')


if __name__ == '__main__':
    main()
