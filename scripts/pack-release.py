#!/usr/bin/env python3
"""Pack CI's existing Veil artifacts without rebuilding or including tests/examples."""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def copy_sources(root, project):
    project.mkdir(parents=True, exist_ok=True)
    for name in ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'Veil.lean']:
        shutil.copyfile(root / name, project / name)
    shutil.copytree(root / 'Veil', project / 'Veil')
    shutil.copytree(root / 'widget', project / 'widget', ignore=shutil.ignore_patterns(
        'node_modules', 'dist', '*.hash'))
    (project / '.lake').mkdir(exist_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    output = (args.output_dir or root / '.lake' / 'releases').resolve()
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='veil-release-build-') as directory:
        project = Path(directory)
        copy_sources(root, project)
        (project / '.lake' / 'packages').symlink_to(root / '.lake' / 'packages',
                                                  target_is_directory=True)
        # Select artifacts for current source modules, excluding removed modules,
        # tests, examples, and old widget outputs from the CI build directory.
        for source in [root / 'Veil.lean', *(root / 'Veil').rglob('*.lean')]:
            module = source.relative_to(root).with_suffix('')
            for directory in ['lib/lean', 'ir']:
                prefix = root / '.lake' / 'build' / directory / module
                for artifact in prefix.parent.glob(prefix.name + '.*'):
                    if artifact.is_file():
                        destination = project / artifact.relative_to(root)
                        destination.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copyfile(artifact, destination)
        # Validate the selected files; missing artifacts must fail, not rebuild
        # or be silently repaired from another cache.
        env = {**os.environ, 'LAKE_ARTIFACT_CACHE': 'false', 'LAKE_CACHE_DIR': '',
               'LAKE_NO_CACHE': 'true'}
        subprocess.run(['lake', '--no-build', 'build', 'Veil'],
                       cwd=project, env=env, check=True)
        subprocess.run(['lake', 'pack'], cwd=project, env=env, check=True)
        archives = list((project / '.lake').glob('veil-*.tar.gz'))
        if len(archives) != 1:
            raise RuntimeError(f'Expected one release archive, got {archives}')
        destination = output / archives[0].name
        shutil.copyfile(archives[0], destination)
        print(f'Release archive: {destination}', flush=True)


if __name__ == '__main__':
    main()
