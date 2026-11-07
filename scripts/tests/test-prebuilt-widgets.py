#!/usr/bin/env python3
"""Check widget reuse at a fresh path without Node/npm, plus source/mode invalidation.

Run after Lake has fetched dependencies (e.g. after `lake build`). Only the widget
target is built; dependency checkouts are shared, but no root build cache or npm
installation is copied into the temporary project.
"""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import json


def main():
    root = Path(__file__).resolve().parents[2]
    with tempfile.TemporaryDirectory(prefix='veil-prebuilt-widgets-') as directory:
        project = Path(directory)
        for name in ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain']:
            shutil.copyfile(root / name, project / name)
        shutil.copytree(root / 'widget', project / 'widget',
                        ignore=shutil.ignore_patterns('node_modules', 'dist'))
        (project / '.lake').mkdir()
        (project / '.lake' / 'packages').symlink_to(root / '.lake' / 'packages',
                                                  target_is_directory=True)
        blockers = project / 'no-node'
        blockers.mkdir()
        for name in ['npm', 'node', 'npx']:
            executable = blockers / name
            executable.write_text('#!/bin/sh\necho "Unexpected Node/npm invocation" >&2\nexit 99\n')
            executable.chmod(0o755)
        env = {**os.environ, 'PATH': str(blockers) + os.pathsep + os.environ['PATH']}

        def build(target, *, stale=False):
            result = subprocess.run(
                ['lake', '-KerrorOnBuild=unexpected-widget-rebuild', 'build', target],
                cwd=project, env=env, text=True, capture_output=True)
            output = result.stdout + result.stderr
            if stale:
                assert result.returncode != 0 and 'unexpected-widget-rebuild' in output, output
            else:
                assert result.returncode == 0, output
            assert 'Unexpected Node/npm invocation' not in output, output

        build('widgetJsAll')
        build('widgetJsAllDev', stale=True)
        package_json = project / 'widget' / 'package.json'
        original_package = package_json.read_bytes()
        package = json.loads(original_package)
        package['scripts']['build'] += ' --unexpected-build-script-change'
        package_json.write_text(json.dumps(package))
        build('widgetJsAll', stale=True)
        package_json.write_bytes(original_package)
        lock = project / 'widget' / 'package-lock.json'
        original_lock = lock.read_bytes()
        # Even a leftover hash sidecar must not mask edits to the lockfile input.
        (lock.parent / 'package-lock.json.hash').write_text('0000000000000000')
        lock.write_bytes(original_lock + b'\n')
        build('widgetJsAll', stale=True)
        lock.write_bytes(original_lock)
        build('widgetJsAll')
        source = next((project / 'widget' / 'src').glob('*.tsx'))
        source.write_text(source.read_text() + '\n// Check source invalidation.\n')
        build('widgetJsAll', stale=True)
    print('Prebuilt widgets work without Node/npm; source and mode changes invalidate them.')


if __name__ == '__main__':
    main()
