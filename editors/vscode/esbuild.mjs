// Bundles the extension, its webview, and the tests.
//   node esbuild.mjs [--watch] [--production]
//   node esbuild.mjs --tests
import * as esbuild from 'esbuild';
import { createRequire } from 'module';
import * as path from 'path';
import { fileURLToPath } from 'url';

const watch = process.argv.includes('--watch');
const production = process.argv.includes('--production');
const tests = process.argv.includes('--tests');

const here = path.dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);
const widgetSources = path.resolve(here, '../../widget/src');

/** Lets the panel import the widgets of the Lean infoview as `@veil/widget/<file>` (see
 * `webview/widget.d.ts`). They get this package's React, since the copy in `widget/node_modules`
 * would break hooks, and a stub for `htmlDisplay`, since the panel has no Lean server. */
const widgets = {
  name: 'veil-widgets',
  setup(build) {
    build.onResolve({ filter: /^@veil\/widget\// }, args =>
      ({ path: path.join(widgetSources, `${args.path.slice('@veil/widget/'.length)}.tsx`) }));
    build.onResolve({ filter: /^\.\/htmlDisplay$/ }, args => args.importer.startsWith(widgetSources)
      ? { path: path.join(here, 'webview', 'htmlDisplayStub.tsx') }
      : undefined);
    build.onResolve({ filter: /^react(-dom)?(\/.*)?$/ }, args => ({ path: require.resolve(args.path) }));
  },
};

const common = {
  bundle: true,
  sourcemap: !production,
  minify: production,
  logLevel: 'info',
  jsx: 'automatic',
  plugins: [widgets],
};

const node = { ...common, platform: 'node', format: 'cjs', target: 'node16' };

const builds = tests
  ? [{ ...node, entryPoints: ['test/runTests.ts'], outfile: 'out/test/runTests.js' }]
  : [
      { ...node, entryPoints: ['src/extension.ts'], outfile: 'dist/extension.js', external: ['vscode'] },
      {
        ...common,
        entryPoints: ['webview/main.tsx'],
        outfile: 'dist/webview.js',
        platform: 'browser',
        format: 'iife',
        target: 'es2020',
        define: { 'process.env.NODE_ENV': JSON.stringify(production ? 'production' : 'development') },
      },
    ];

if (watch) {
  for (const options of builds) await (await esbuild.context(options)).watch();
} else {
  await Promise.all(builds.map(options => esbuild.build(options)));
}
