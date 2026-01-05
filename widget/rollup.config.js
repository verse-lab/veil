import { glob } from 'glob';
import { nodeResolve } from '@rollup/plugin-node-resolve';
import commonjs from '@rollup/plugin-commonjs';
import replace from '@rollup/plugin-replace';
import terser from '@rollup/plugin-terser';

/** @type {(_: any) => import('rollup').RollupOptions} */
export default _cliArgs => {
    const inputs = glob.sync('dist/*.js')

    const isProduction = process.env.NODE_ENV && process.env.NODE_ENV === 'production';
    const configForInput = fname => ({
        input: fname,
        output: {
            dir: '../.lake/build/js',
            format: 'es',
            // Setting `global` makes some CommonJS modules work
            intro: 'const global = window;',
            sourcemap: isProduction ? false : 'inline',
            plugins: isProduction ? [ terser() ] : [],
            compact: isProduction
        },
        external: [
            'react',
            'react-dom',
            'react/jsx-runtime',
            '@leanprover/infoview',
        ],
        plugins: [
            nodeResolve({
                browser: true
            }),
            replace({
                'typeof window': JSON.stringify('object'),
                'process.env.NODE_ENV': JSON.stringify(process.env.NODE_ENV),
                preventAssignment: true
            }),
            commonjs({
                // Block Node.js modules from being hoisted (we're running in browser)
                ignore: [
                    'process', 'events', 'stream', 'util', 'path', 'buffer', 'querystring', 'url',
                    'string_decoder', 'punycode', 'http', 'https', 'os', 'assert', 'constants',
                    'timers', 'console', 'vm', 'zlib', 'tty', 'domain', 'dns', 'dgram', 'child_process',
                    'cluster', 'module', 'net', 'readline', 'repl', 'tls', 'fs', 'crypto', 'perf_hooks',
                ],
            })
        ],
    })

    // Each widget module is bundled into a standalone .js file.
    // We return an array of configs so Rollup runs on each module separately,
    // avoiding code splitting into chunk.js files.
    // TypeScript is compiled first with tsc, then Rollup bundles the JS outputs.
    return inputs.map(configForInput)
}
