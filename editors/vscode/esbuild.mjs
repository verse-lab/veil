// Bundles the extension, its webview, and the tests.
//   node esbuild.mjs [--watch] [--production]
//   node esbuild.mjs --tests
import * as esbuild from 'esbuild';

const watch = process.argv.includes('--watch');
const production = process.argv.includes('--production');
const tests = process.argv.includes('--tests');

const common = {
  bundle: true,
  sourcemap: !production,
  minify: production,
  logLevel: 'info',
};

const node = { ...common, platform: 'node', format: 'cjs', target: 'node16' };

const builds = tests
  ? [{ ...node, entryPoints: ['test/runTests.ts'], outfile: 'out/test/runTests.js', jsx: 'automatic' }]
  : [
      { ...node, entryPoints: ['src/extension.ts'], outfile: 'dist/extension.js', external: ['vscode'] },
      {
        ...common,
        entryPoints: ['webview/main.tsx'],
        outfile: 'dist/webview.js',
        platform: 'browser',
        format: 'iife',
        target: 'es2020',
        jsx: 'automatic',
        define: { 'process.env.NODE_ENV': JSON.stringify(production ? 'production' : 'development') },
      },
    ];

if (watch) {
  for (const options of builds) await (await esbuild.context(options)).watch();
} else {
  await Promise.all(builds.map(options => esbuild.build(options)));
}
