// Checks that the version of the extension is 0.N.x for its IDE_PROTOCOL N (see "Versions" in
// PUBLISHING.md). `vscode:prepublish` and `npm test` run it.
import { readFileSync } from 'fs';

const read = file => readFileSync(new URL(file, import.meta.url), 'utf8');
const { version } = JSON.parse(read('./package.json'));
const protocol = /^export const IDE_PROTOCOL = (\d+);$/m.exec(read('./src/compatibility.ts'))?.[1];
if (protocol === undefined) {
  console.error('checkVersion.mjs: found no `export const IDE_PROTOCOL = <number>;` in src/compatibility.ts');
  process.exit(1);
}
if (/^0\.(\d+)\.\d+$/.exec(version)?.[1] !== protocol) {
  console.error(`The version of the extension, ${version}, must be 0.${protocol}.x for IDE protocol ${protocol} ` +
    '(see PUBLISHING.md).');
  process.exit(1);
}
