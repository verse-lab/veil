#!/usr/bin/env python3
"""Restore a release at a fresh source path and require it to work without rebuilding.

Reuse the dependencies already built by CI. Independent dependency builds were
validated separately; this is a cheap packaging/restore smoke check.
"""

import argparse
import importlib.util
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    spec = importlib.util.spec_from_file_location('pack_release', root / 'scripts' / 'pack-release.py')
    pack = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(pack)
    with tempfile.TemporaryDirectory(prefix='veil-release-restore-') as directory:
        project = Path(directory)
        pack.copy_sources(root, project)
        (project / '.lake' / 'packages').symlink_to(root / '.lake' / 'packages',
                                                  target_is_directory=True)
        archive = args.archive.resolve()
        shutil.copyfile(archive, project / '.lake' / archive.name)
        env = {**os.environ, 'LAKE_ARTIFACT_CACHE': 'false', 'LAKE_CACHE_DIR': '',
               'LAKE_NO_CACHE': 'true'}
        subprocess.run(['lake', 'unpack'], cwd=project, env=env, check=True)
        subprocess.run(['lake', '--no-build', 'build'], cwd=project, env=env, check=True)
    print('Release archive restored successfully without rebuilding.')


if __name__ == '__main__':
    main()
