// `npm run publish:marketplace [-- patch]` (see PUBLISHING.md). Other bumps are refused: the minor
// version is the IDE protocol, and vsce runs `vscode:prepublish`, which checks the version, before it
// bumps the version.
import { spawnSync } from 'child_process';

const args = process.argv.slice(2);
if (args.length > 1 || (args.length === 1 && args[0] !== 'patch')) {
  console.error(`Publish with "patch" or without an argument, not "${args.join(' ')}": the minor version is ` +
    'the IDE protocol (see PUBLISHING.md).');
  process.exit(1);
}
const vsce = spawnSync('vsce', ['publish', '--no-dependencies', '--no-git-tag-version', ...args],
  { stdio: 'inherit', shell: process.platform === 'win32' });
if (vsce.error) console.error(`Could not run vsce: ${vsce.error.message}`);
process.exit(vsce.status ?? 1);
