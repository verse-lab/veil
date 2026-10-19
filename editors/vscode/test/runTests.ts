// The tests of the parts of the extension that do not use VS Code: `npm test`. The tests with
// binaries first build those of `fixtures/RunnerFixture.lean` with Lean, which needs `lake` and a
// built Veil. Set VEIL_SKIP_BINARY_TESTS=1 to skip them.
import * as assert from 'assert';
import { spawnSync } from 'child_process';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as React from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { BUILT_PREFIX, ReportedMessage, Severity, buildStatus, findBuildCommands, findVeilModules } from '../src/buildCommands';
import { ConfigTemplate, configCommand, configFileFor, configHeader, isOfModule, snippetText } from '../src/configTemplate';
import { Progress, StartReport, describeResult, modelCheckMetrics, parseProgressLine, parseStartLine } from '../src/protocol';
import { FORMAT_VERSION, ResultStore, RunSource, freshness, parseRunFile } from '../src/resultStore';
import { CheckerRun, parallelArgs, parseRunOptions } from '../src/runner';
import { HistoryPoint, ModuleSources, RunSnapshot, describeRun, recordHistory } from '../src/snapshot';
import { NoRun, RunView, RunViewProps } from '../webview/view';
import { pathToFileURL } from 'url';
import { LeanServer } from './leanServer';

interface Test {
  name: string;
  run: () => void | Promise<void>;
}
const tests: Test[] = [];
const test = (name: string, run: Test['run']) => tests.push({ name, run });

// ---- Finding commands ----

test('finds commands and where they end', () => {
  const text = [
    'module',
    '#model_check_build Foo { n := Fin 2 }',
    '  { limit := 2 }',
    '',
    '  #model_check_build Bar.Baz {}',
    'def x := 1',
  ].join('\n');
  assert.deepStrictEqual(findBuildCommands(text), [
    { line: 1, character: 0, endLine: 3, module: 'Foo', command: '#model_check_build Foo { n := Fin 2 } { limit := 2 }' },
    { line: 4, character: 2, endLine: 4, module: 'Bar.Baz', command: '#model_check_build Bar.Baz {}' },
  ]);
});

test('leaves out commands in comments and strings', () => {
  const text = [
    '-- #model_check_build InLineComment {}',
    '/- #model_check_build InBlockComment {}',
    '#model_check_build StillInBlockComment {}',
    '/- nested -/',
    '-/',
    '/-- A docstring',
    '#model_check_build InDocstring {}',
    '-/',
    'def s := "',
    '#model_check_build InString {}"',
    '#model_check_build Real {}',
    'x #model_check_build NotAtLineStart {}',
    '#model_check_builder NotTheKeyword {}',
  ].join('\n');
  assert.deepStrictEqual(findBuildCommands(text).map(site => site.module), ['Real']);
});

test('finds modules and the commands of them that a config file needs', () => {
  const text = [
    'veil module Paxos',            // 0
    'type node',
    '-- #gen_executable',
    '#gen_spec',                    // 3
    '#gen_executable -borrowArgs',  // 4
    'end Paxos',                    // 5
    '/- veil module InComment -/',
    'veil module Ring',             // 7
    'end Other',
  ].join('\n');
  assert.deepStrictEqual(findVeilModules(text), [
    { line: 0, character: 0, name: 'Paxos', genSpecLine: 3, genExecutableLine: 4, endLine: 5 },
    { line: 7, character: 0, name: 'Ring' },
  ]);
});

// ---- Config templates ----

const template: ConfigTemplate = {
  module: 'CheckedElsewhere',
  import: 'VeilTest.Regression.ModelCheckBuildHelper',
  instantiation: [{ name: 'node', value: 'Fin 2' }, { name: 'NodeSet', value: '_' }],
  theory: [{ name: 'limit', value: '_' }],
};

test('writes the config file of a template, with placeholders for its values', () => {
  assert.strictEqual(configHeader(template), 'module\n\npublic import Veil\npublic import VeilTest.Regression.ModelCheckBuildHelper\n\n');
  const parts = configCommand(template);
  assert.deepStrictEqual(parts.filter(part => 'placeholder' in part), [{ placeholder: 'Fin 2' }, { placeholder: '_' }, { placeholder: '_' }]);
  assert.strictEqual(snippetText(parts),
    '#model_check_build CheckedElsewhere\n  { node := Fin 2, NodeSet := _ }\n  { limit := _ }\n');
  // A module without sorts has an empty instantiation, and the theory is left out when it is empty
  assert.strictEqual(snippetText(configCommand({ ...template, instantiation: [], theory: [] })),
    '#model_check_build CheckedElsewhere\n  {}\n');
});

test('puts a new config file next to its module, and finds the configs of a module', () => {
  assert.strictEqual(configFileFor('/repo/Examples/Paxos.lean'), '/repo/Examples/MCPaxos.lean');
  assert.ok(isOfModule('Paxos', 'Paxos'));
  assert.ok(isOfModule('Paxos', 'Examples.Paxos'));
  assert.ok(isOfModule('Examples.Paxos', 'Paxos'));
  assert.ok(!isOfModule('Raft', 'Paxos'));
});

// ---- Build status ----

const site = { line: 1, character: 0, endLine: 3, module: 'Foo', command: '#model_check_build Foo {}' };
const message = (line: number, severity: Severity, text: string): ReportedMessage => ({ line, severity, message: text });

test('a command is built once Lean reports its binary', () => {
  assert.deepStrictEqual(buildStatus(site, [message(1, 'information', `${BUILT_PREFIX}/tmp/a b/checker\n`)]),
    { kind: 'built', binary: '/tmp/a b/checker' });
});

test('an error in a command means that its binary was not built', () => {
  assert.deepStrictEqual(
    buildStatus(site, [message(1, 'information', `${BUILT_PREFIX}/tmp/old`), message(2, 'error', 'failed to synthesize')]),
    { kind: 'failed', message: 'failed to synthesize' });
});

test('the messages of other commands do not count', () => {
  assert.deepStrictEqual(
    buildStatus(site, [message(0, 'error', 'elsewhere'), message(4, 'information', `${BUILT_PREFIX}/tmp/other`)]),
    { kind: 'pending' });
});

// ---- Output of binaries ----

/** A line of progress, as a binary prints it */
function progressLine(elapsedMs: number, distinctStates: number): string {
  return JSON.stringify({
    compilationStatus: { status: 'none' },
    details: { modelCheck: { metrics: {
      actionStats: [{ distinctStates, label: {
        $veil: 'ctor', type: 'M.Label', name: 'finish', args: [{ name: 'n', value: '0' }],
      }, statesGenerated: distinctStates }],
      allActionLabels: [], diameter: 1, distinctStates, history: [], queue: 2, statesFound: distinctStates,
    } } },
    elapsedMs, isCancelled: false, isRunning: true, startTimeMs: 3595464416, status: 'Running...',
  });
}

test('parses lines of progress', () => {
  const progress = parseProgressLine(progressLine(5, 3));
  assert.ok(progress);
  assert.strictEqual(modelCheckMetrics(progress)?.distinctStates, 3);
  assert.strictEqual(parseProgressLine('PANIC at foo'), undefined);
  assert.strictEqual(parseProgressLine('{"other": 1}'), undefined);
});

test('parses the start report', () => {
  const line = '{"start":{"actionLabels":["finish","reset"]}}';
  assert.deepStrictEqual(parseStartLine(line), { actionLabels: ['finish', 'reset'] });
  assert.strictEqual(parseProgressLine(line), undefined);
  assert.strictEqual(parseStartLine(progressLine(5, 3)), undefined);
});

test('describes results as Lean does', () => {
  assert.deepStrictEqual(describeResult({ result: 'no_violation_found', explored_states: 4 }),
    { kind: 'success', text: 'No violation (explored 4 states)' });
  assert.deepStrictEqual(
    describeResult({ result: 'found_violation', violation: { kind: 'safety_failure', violates: ['bounded'] } }),
    { kind: 'violation', text: 'Violation: safety_failure (violates: bounded)' });
  assert.strictEqual(describeResult({ error: 'boom' }).kind, 'error');
});

test('keeps a point of history about every second', () => {
  const history: HistoryPoint[] = [];
  for (const time of [0, 300, 600, 1200, 1500]) recordHistory(history, parseProgressLine(progressLine(time, 1)) as Progress);
  assert.deepStrictEqual(history.map(point => point.timeMs), [0, 1200, 1500]);
});

test('reads the options that the user types for a run', () => {
  const defaults = { thresholdToParallel: 20, numSubSteps: 1 };
  assert.deepStrictEqual(parseRunOptions('4', defaults, 8), ['4', '20', '1']);
  assert.deepStrictEqual(parseRunOptions(' 4 50 2 ', defaults, 8), ['4', '50', '2']);
  assert.deepStrictEqual(parseRunOptions('0', defaults, 8), ['8', '20', '1']);
  assert.deepStrictEqual(parseRunOptions('1 50', defaults, 8), []);
  for (const wrong of ['', 'four', '4 -1', '4 20 1 1', '4 20 0']) {
    assert.ok(!Array.isArray(parseRunOptions(wrong, defaults, 8)), `${JSON.stringify(wrong)} is not options`);
  }
});

test('passes the parallel settings as arguments', () => {
  assert.deepStrictEqual(parallelArgs(0, 20, 1, 8), ['8', '20', '1']);
  assert.deepStrictEqual(parallelArgs(4, 20, 2, 8), ['4', '20', '2']);
  assert.deepStrictEqual(parallelArgs(1, 20, 1, 8), []);
  assert.deepStrictEqual(parallelArgs(0, 20, 1, 1), []);
});

// ---- The panel ----

function snapshot(fields: Partial<RunSnapshot>): RunSnapshot {
  return {
    module: 'Paxos', source: 'MCPaxos.lean:12', binary: '/tmp/checker', args: ['8', '20', '1'],
    status: 'running', startedAt: 0, history: [], ...fields,
  };
}

/** The panel for `run`, 63 seconds after it started */
function render(run: RunSnapshot): string {
  return renderToStaticMarkup(React.createElement(RunView, { run, now: 63_000 }));
}

function assertShows(html: string, texts: string[]): void {
  for (const text of texts) assert.ok(html.includes(text), `the panel does not show ${JSON.stringify(text)}`);
}

const point = (timeMs: number): HistoryPoint => ({ timeMs, diameter: 1, statesFound: 2, distinctStates: 2, queue: 1 });

test('the panel shows the progress of a running check', () => {
  const progress: Progress = {
    status: 'Running...', isRunning: true, isCancelled: false, elapsedMs: 60_000,
    details: { modelCheck: { metrics: {
      diameter: 7, statesFound: 123456, distinctStates: 65432, queue: 99,
      allActionLabels: ['send', 'decide', 'prepare'],
      actionStats: [
        { label: { $veil: 'ctor', type: 'Paxos.Label', name: 'send',
          args: [{ name: 'from', value: '0' }, { name: 'to', value: '1' }] },
          statesGenerated: 10, distinctStates: 5 },
        { label: { $veil: 'ctor', type: 'Paxos.Label', name: 'send',
          args: [{ name: 'from', value: '1' }, { name: 'to', value: '0' }] },
          statesGenerated: 4, distinctStates: 2 },
        { label: { $veil: 'ctor', type: 'Paxos.Label', name: 'decide', args: [] },
          statesGenerated: 0, distinctStates: 0 },
      ],
    } } },
  };
  assertShows(render(snapshot({ progress, history: [point(0), point(1000)] })), [
    'Paxos', 'MCPaxos.lean:12', 'Running...', 'Stop', '8 workers', 'Diameter:', '123,456', '65,432',
    'Elapsed time:', '1m 3.0s', 'Metrics History (2 samples, 1.0s)', 'Graph', 'Table', 'Copy JSON',
    'States Found', 'Queue Size', '<path class="chart-line"', 'Action Coverage (2 actions',
    '2 never enabled', 'Never enabled: decide, prepare', 'send', 'from=0, to=1',
  ]);
});

test('the panel sorts multiple action arguments numerically', () => {
  const progress = parseProgressLine(progressLine(1, 1))!;
  modelCheckMetrics(progress)!.actionStats = [[10, 1], [2, 10], [2, 2], [1, 10]].map(([previous, n]) => ({
    label: { $veil: 'ctor', type: 'M.Label', name: 'finishAfter',
      args: [{ name: 'previous', value: previous }, { name: 'n', value: n }] },
    statesGenerated: 1, distinctStates: 1,
  }));
  const html = render(snapshot({ progress }));
  const variants = [[1, 10], [2, 2], [2, 10], [10, 1]].map(([previous, n]) =>
    `<span>previous=${previous}, n=${n}</span>`);
  assertShows(html, variants);
  for (let i = 1; i < variants.length; i++) {
    assert.ok(html.indexOf(variants[i - 1]) < html.indexOf(variants[i]));
  }
});

test('the panel shows the result of a finished check with the widget of the infoview', () => {
  const violation = { result: 'found_violation', violation: { kind: 'safety_failure', violates: ['bounded'] } };
  const html = render(snapshot({ status: 'finished', endedAt: 5000, result: violation, args: [] }));
  assertShows(html, ['Done!', 'sequential', 'Safety Violation Found', 'Violated properties', 'bounded', 'No trace available']);
  assert.ok(!html.includes('>Stop<'));
  const success = { result: 'no_violation_found', explored_states: 4, termination_reason: { kind: 'explored_all_reachable_states' } };
  assertShows(render(snapshot({ status: 'finished', endedAt: 5000, result: success })),
    ['No Violation Found', 'Explored all reachable states (4)']);
});

test('the panel shows why a run failed or that it was stopped', () => {
  assertShows(render(snapshot({ status: 'failed', endedAt: 5000, error: 'The model checker exited with code 1.' })),
    ['Failed', 'exited with code 1']);
  assertShows(render(snapshot({ status: 'stopped', endedAt: 5000 })), ['Stopped']);
});

test('the panel says when no check has run', () => {
  assertShows(renderToStaticMarkup(React.createElement(NoRun)), ['#model_check_build']);
});

test('the panel tells a saved run, or one from a file, from a run of this window', () => {
  const view = (props: Partial<RunViewProps>) => renderToStaticMarkup(React.createElement(RunView,
    { run: snapshot({ status: 'stopped', endedAt: 5000 }), now: 63_000, ...props }));
  const live = view({});
  assertShows(live, ['Export...', 'Full output']);
  assert.ok(!live.includes('Saved result'));
  const saved = view({ origin: 'saved' });
  assertShows(saved, ['Saved result', 'Export...']);
  assert.ok(!saved.includes('Full output'), 'the output channel has the run of this window only');
  assert.ok(!saved.includes('outdated'));
  assertShows(view({ origin: 'saved', outdated: true }), ['Saved result · outdated: the model checker has changed']);
  assertShows(view({ origin: 'file', fileName: 'paxos.json', canRunAgain: false }),
    ['Opened from paxos.json', '<button class="primary" disabled="">Check again</button>']);
  // A running check can be neither run again nor exported
  const running = view({ run: snapshot({}) });
  assertShows(running, ['<button class="primary" disabled="">Check again</button>']);
  assert.ok(!running.includes('Export...'));
});

test('the panel links the actions and properties of a run to their sources', () => {
  const label = { $veil: 'ctor', type: 'M.Label', name: 'finish', args: [{ name: 'n', value: 0 }] };
  const progress: Progress = {
    status: 'Done', isRunning: false, isCancelled: false, elapsedMs: 10,
    details: { modelCheck: { metrics: {
      diameter: 1, statesFound: 2, distinctStates: 2, queue: 0, allActionLabels: [],
      actionStats: [{ label, statesGenerated: 1, distinctStates: 1 }],
    } } },
  };
  const result = {
    result: 'found_violation', violation: { kind: 'safety_failure', violates: ['bounded'] },
    trace: { theory: {}, states: [
      { transition: 'after_init', index: 0, fields: { finished: [] } },
      { transition: label, index: 1, fields: { finished: ['0'] } },
    ] },
  };
  const location = (name: string, line: number) => ({ name, file: '/repo/M.lean', line, character: 0 });
  const sources = { actions: [location('after_init', 3), location('finish', 7)], properties: [location('bounded', 12)] };
  const run = snapshot({ status: 'finished', endedAt: 5000, progress, result });
  const link = (text: string) => `<a class="source-link" title="Go to the source">${text}</a>`;
  // The coverage, the steps of the trace, and the violated property
  assertShows(render({ ...run, sources }), [link('finish'), link('after_init'), link('finish(n = 0)'), link('bounded')]);
  // As in the infoview, nothing links without sources
  assert.ok(!render(run).includes('class="source-link"'));
});

test('trace links preserve leading underscores in source names without changing displayed labels', () => {
  for (const name of ['_start', '__start']) {
    const result = {
      result: 'found_violation', violation: { kind: 'safety_failure', violates: [] },
      trace: { theory: {}, states: [
        { transition: name, index: 0, fields: {} },
        { transition: { $veil: 'ctor', type: 'M.Label', name, args: [{ name: 'self', value: 1 }] },
          index: 1, fields: {} },
        { transition: { [name]: { self: 2 } }, index: 2, fields: {} },
      ] },
    };
    const sources = {
      actions: [{ name, file: '/repo/M.lean', line: 7, character: 0 }], properties: [],
    };
    const html = render({ ...snapshot({ status: 'finished', endedAt: 5000, result }), sources });
    const link = (text: string) => `<a class="source-link" title="Go to the source">${text}</a>`;
    assertShows(html, [link(name), link(`${name.slice(1)}(self = 1)`), link(`${name.slice(1)}(self = 2)`)]);
  }
});

test('describes how runs ended', () => {
  assert.deepStrictEqual(describeRun(snapshot({ status: 'failed', error: 'exited with code 1.\nPANIC' })),
    { kind: 'failed', text: 'Failed: exited with code 1.' });
  assert.strictEqual(describeRun(snapshot({ status: 'stopped' })).kind, 'stopped');
  assert.strictEqual(describeRun(snapshot({ status: 'finished', result: { result: 'no_violation_found', explored_states: 4 } })).kind,
    'success');
});

// ---- Saved runs ----

const finished = (endedAt: number) => snapshot({
  status: 'finished', endedAt, result: { result: 'no_violation_found', explored_states: 4 },
});
const sourceOf = (file: string, command = '#model_check_build Paxos {}'): RunSource => ({ file, command });

function withStoreDir(run: (dir: string) => Promise<void>): () => Promise<void> {
  return async () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'veil-results-'));
    try {
      await run(dir);
    } finally {
      fs.rmSync(dir, { recursive: true, force: true });
    }
  };
}

test('saves the last run of each command, for the next window', withStoreDir(async dir => {
  const store = new ResultStore(dir);
  await store.save(sourceOf('file:///a.lean'), finished(1000));
  await store.save(sourceOf('file:///a.lean'), snapshot({ status: 'stopped', endedAt: 2000 }));
  await store.save(sourceOf('file:///b.lean'), finished(3000));
  const later = new ResultStore(dir);
  await later.load();
  assert.deepStrictEqual(later.summary(sourceOf('file:///a.lean')),
    { source: sourceOf('file:///a.lean'), binary: '/tmp/checker', outcome: 'stopped', text: 'Stopped', endedAt: 2000 });
  assert.strictEqual(later.summary(sourceOf('file:///a.lean', '#model_check_build Paxos { n := 3 }')), undefined);
  assert.deepStrictEqual(later.newest()?.source, sourceOf('file:///b.lean'));
  assert.strictEqual((await later.read(sourceOf('file:///b.lean')))?.run.endedAt, 3000);
}));

test('keeps only the newest runs', withStoreDir(async dir => {
  const store = new ResultStore(dir, () => 2);
  for (const [i, file] of ['file:///a.lean', 'file:///b.lean', 'file:///c.lean'].entries()) {
    await store.save(sourceOf(file), finished(1000 * (i + 1)));
  }
  assert.strictEqual(store.summary(sourceOf('file:///a.lean')), undefined);
  assert.strictEqual(await store.read(sourceOf('file:///a.lean')), undefined);
  assert.deepStrictEqual(fs.readdirSync(dir).sort().filter(name => name !== 'index.json').length, 2);
}));

test('applies changed saved-result limits on the next save', withStoreDir(async dir => {
  let limit = 2;
  const store = new ResultStore(dir, () => limit);
  const a = sourceOf('file:///a.lean');
  const b = sourceOf('file:///a.lean', '#model_check_build Paxos { n := 3 }');
  const c = sourceOf('file:///b.lean');
  await store.save(a, finished(1000));
  await store.save(b, finished(2000));
  limit = 3;
  await store.save(c, finished(3000));
  assert.ok(store.summary(a));
  limit = 1;
  assert.ok(store.summary(a));
  await store.save(b, finished(4000));
  assert.strictEqual(store.summary(a), undefined);
  assert.strictEqual(store.summary(c), undefined);
  assert.strictEqual(await store.read(a), undefined);
  assert.strictEqual(await store.read(c), undefined);
  const later = new ResultStore(dir);
  await later.load();
  assert.strictEqual(later.summary(a), undefined);
  assert.strictEqual(later.summary(c), undefined);
  assert.strictEqual((await later.read(b))?.run.endedAt, 4000);
}));

test('uses the default for invalid saved-result limits', withStoreDir(async dir => {
  let limit = 2;
  const store = new ResultStore(dir, () => limit);
  const a = sourceOf('file:///a.lean');
  const b = sourceOf('file:///b.lean');
  await store.save(a, finished(1000));
  for (limit of [0, -1, 1.5, NaN]) {
    await store.save(b, finished(2000));
    assert.ok(store.summary(a));
    assert.strictEqual((await store.read(a))?.run.endedAt, 1000);
    assert.strictEqual((await store.read(b))?.run.endedAt, 2000);
  }
}));

test('starts with no saved runs from an index it cannot read', withStoreDir(async dir => {
  fs.writeFileSync(path.join(dir, 'index.json'), '{ not json');
  const store = new ResultStore(dir);
  await store.load();
  assert.strictEqual(store.newest(), undefined);
  fs.writeFileSync(path.join(dir, 'index.json'), JSON.stringify({ formatVersion: FORMAT_VERSION + 1, runs: [] }));
  await store.load();
  assert.strictEqual(store.newest(), undefined);
}));

test('tells whether a saved run is of the binary that Lean builds now', () => {
  const built = (binary: string) => ({ kind: 'built' as const, binary });
  const saved = '/repo/.lake/model_checkers/MC_model_check_build_123';
  assert.strictEqual(freshness(saved, built(saved)), 'current');
  // The hash in the name is what counts, e.g. for a run exported on another machine
  assert.strictEqual(freshness(saved, built('/elsewhere/.lake/model_checkers/MC_model_check_build_123')), 'current');
  assert.strictEqual(freshness(saved, built('/repo/.lake/model_checkers/MC_model_check_build_456')), 'outdated');
  assert.strictEqual(freshness(saved, { kind: 'pending' }), 'unknown');
  assert.strictEqual(freshness(saved, { kind: 'failed', message: 'error' }), 'unknown');
  assert.strictEqual(freshness('', built(saved)), 'unknown');
  assert.strictEqual(freshness(undefined as unknown as string, built(saved)), 'unknown');
});

test('opens exported runs, and the results that binaries print', () => {
  const exported = { formatVersion: FORMAT_VERSION, source: sourceOf('file:///a.lean'), run: finished(1000) };
  assert.deepStrictEqual(parseRunFile(JSON.stringify(exported), '/tmp/a.json', 0), exported);
  const printed = parseRunFile('{"result": "no_violation_found", "explored_states": 4}', '/tmp/ci-run.json', 7000);
  assert.strictEqual(printed?.source, undefined);
  assert.deepStrictEqual([printed?.run.module, printed?.run.status, printed?.run.endedAt], ['ci-run.json', 'finished', 7000]);
  assert.strictEqual(parseRunFile('{"other": 1}', '/tmp/x.json', 0), undefined);
  assert.strictEqual(parseRunFile('not json', '/tmp/x.json', 0), undefined);
});

// ---- Running binaries ----

const repoRoot = path.resolve(__dirname, '../../../..');
const fixture = path.join('editors', 'vscode', 'test', 'fixtures', 'RunnerFixture.lean');

/** The binaries of the fixture's commands, by the 1-based line of the command. Lean reports them as
 * the extension reads them, but through `lean --json` rather than as diagnostics. */
function buildFixture(): Map<number, string> {
  const lean = spawnSync('lake', ['env', 'lean', '--json', fixture],
    { cwd: repoRoot, encoding: 'utf8', maxBuffer: 256 * 1024 * 1024 });
  if (lean.error) throw lean.error;
  const binaries = new Map<number, string>();
  const errors: string[] = [];
  for (const line of lean.stdout.split('\n')) {
    if (!line.startsWith('{')) continue;
    const reported = JSON.parse(line) as { severity: string; pos: { line: number }; data: string };
    if (reported.severity === 'information' && reported.data.startsWith(BUILT_PREFIX)) {
      binaries.set(reported.pos.line, reported.data.slice(BUILT_PREFIX.length).trim());
    } else if (reported.severity === 'error') {
      errors.push(reported.data);
    }
  }
  if (lean.status !== 0 || errors.length > 0) {
    throw new Error(`Lean could not build ${fixture}:\n${errors.join('\n')}\n${lean.stdout}\n${lean.stderr}`);
  }
  return binaries;
}

interface FixtureBinaries {
  small: string;
  large: string;
  violating: string;
}

let fixtureBinaries: Promise<FixtureBinaries> | undefined;
function binaries(): Promise<FixtureBinaries> {
  fixtureBinaries ??= (async () => {
    const byLine = buildFixture();
    const sites = findBuildCommands(fs.readFileSync(path.join(repoRoot, fixture), 'utf8'));
    const [small, large, violating] = sites.map(s => byLine.get(s.line + 1));
    if (!small || !large || !violating) {
      throw new Error(`Lean did not report the binaries of ${fixture}: ${JSON.stringify([...byLine])}`);
    }
    return { small, large, violating };
  })();
  return fixtureBinaries;
}

function within<T>(promise: Promise<T>, ms: number, what: string): Promise<T> {
  return Promise.race([
    promise,
    new Promise<T>((_, reject) => setTimeout(() => reject(new Error(`${what} took more than ${ms} ms`)), ms).unref()),
  ]);
}

if (process.env.VEIL_SKIP_BINARY_TESTS !== '1') {
  test('the workspace installer bundles the documentation linked from its README', withStoreDir(async dir => {
    const build = spawnSync(process.execPath, ['esbuild.mjs', '--production'],
      { cwd: path.join(repoRoot, 'editors', 'vscode'), encoding: 'utf8' });
    assert.strictEqual(build.status, 0, build.stderr);
    const bin = path.join(dir, 'bin');
    const workspace = path.join(dir, 'workspace with spaces');
    fs.mkdirSync(bin);
    fs.mkdirSync(workspace);
    const windows = process.platform === 'win32';
    fs.writeFileSync(path.join(bin, windows ? 'npm.cmd' : 'npm'),
      windows ? '@exit /b 0\r\n' : '#!/bin/sh\nexit 0\n', { mode: 0o755 });
    const pathKey = Object.keys(process.env).find(key => key.toLowerCase() === 'path') ?? 'PATH';
    const installed = spawnSync('lake', ['script', 'run', 'veilInstallVSCodeExtension', workspace], {
      cwd: repoRoot, encoding: 'utf8',
      env: { ...process.env, [pathKey]: bin + path.delimiter + (process.env[pathKey] ?? '') },
    });
    assert.strictEqual(installed.status, 0, installed.stdout + installed.stderr);
    const installDir = path.join(workspace, '.vscode', 'extensions', 'veil-model-checker');
    const readme = fs.readFileSync(path.join(installDir, 'README.md'), 'utf8');
    const document = 'ModelChecker-VSCode-Architecture.md';
    for (const link of ['](#model-checker-in-vs-code-architecture)', '](#installing-the-extension)']) {
      assert.ok(readme.includes(link), `the installed README has no documentation anchor ${link}`);
    }
    assert.ok(!readme.includes('../../docs/'));
    assert.ok(readme.endsWith(fs.readFileSync(path.join(repoRoot, 'docs', document), 'utf8')));
  }));

  for (const [name, args] of [['sequential', []], ['parallel', ['2', '1', '1']]] as const) {
    test(`a ${name} binary reports its result`, async () => {
      let start: StartReport | undefined;
      let progress: Progress | undefined;
      const run = new CheckerRun({ binary: (await binaries()).small, args: [...args] },
        { onStart: report => { start = report; }, onProgress: p => { progress = p; } });
      const outcome = await within(run.outcome, 60_000, 'The run');
      assert.strictEqual(outcome.kind, 'finished');
      const result = (outcome as { result: { result: string; explored_states: number } }).result;
      assert.deepStrictEqual([result.result, result.explored_states], ['no_violation_found', 4]);
      // The start report lists all actions, so the panel tells the one that was never enabled
      assert.deepStrictEqual(start?.actionLabels, ['finish', 'finishAfter', 'reset']);
      assert.deepStrictEqual(progress && modelCheckMetrics(progress)?.allActionLabels, []);
      assertShows(render(snapshot({ progress, actionLabels: start?.actionLabels })),
        ['Never enabled: reset', 'finishAfter', '<span>previous=0, n=1</span>', '<span>previous=1, n=0</span>']);
    });
  }

  test('a binary reports a violation with its trace, which the panel shows', async () => {
    const outcome = await within(new CheckerRun({ binary: (await binaries()).violating, args: [] }).outcome,
      60_000, 'The run');
    assert.strictEqual(outcome.kind, 'finished');
    const result = (outcome as { result: { result: string; violation: { violates: string[] }; trace: { states: unknown[] } } }).result;
    assert.deepStrictEqual([result.result, result.violation.violates, result.trace.states.length],
      ['found_violation', ['bounded'], 3]);
    const html = render(snapshot({ status: 'finished', endedAt: 5000, result }));
    assertShows(html,
      // The theory section starts collapsed
      ['Safety Violation Found', 'bounded', 'finished', 'Theory', '3 states in trace']);
    assert.match(html, /finishAfter\((?:previous = 0, n = 1|previous = 1, n = 0)\)/);
  });

  test('a run stops once its stdin is closed', async () => {
    let progress: Progress | undefined;
    let reported!: () => void;
    const firstProgress = new Promise<void>(resolve => { reported = resolve; });
    const run = new CheckerRun({ binary: (await binaries()).large, args: [] }, {
      onProgress: p => {
        progress = p;
        reported();
      },
    });
    await within(firstProgress, 60_000, 'The first progress');
    const stoppedAt = Date.now();
    run.stop();
    const outcome = await within(run.outcome, 10_000, 'The stop');
    assert.strictEqual(outcome.kind, 'stopped');
    // Well before `stop` would kill the binary
    assert.ok(Date.now() - stoppedAt < 1500, `the binary took ${Date.now() - stoppedAt} ms to exit`);
    assert.ok((progress && modelCheckMetrics(progress)?.distinctStates || 0) > 0);
  });

  test('Lean gives the config template of a module, to a request for its kind only', async () => {
    const server = new LeanServer(repoRoot);
    try {
      const initialized = await within(server.request('initialize',
        { processId: process.pid, rootUri: pathToFileURL(repoRoot).href, capabilities: {} }), 60_000, 'Starting Lean');
      const kinds = (initialized as { capabilities: { codeActionProvider: { codeActionKinds: string[] } } })
        .capabilities.codeActionProvider.codeActionKinds;
      assert.ok(kinds.some(kind => 'refactor.veil.modelCheckConfig' === kind ||
        'refactor.veil.modelCheckConfig'.startsWith(`${kind}.`)), 'VS Code must select the Lean code action provider');
      server.notify('initialized', {});
      const file = path.join(repoRoot, 'VeilTest', 'Regression', 'ModelCheckBuildHelper.lean');
      const uri = pathToFileURL(file).href;
      const text = fs.readFileSync(file, 'utf8');
      server.notify('textDocument/didOpen', { textDocument: { uri, languageId: 'lean4', version: 1, text } });
      await within(server.request('textDocument/waitForDiagnostics', { uri, version: 1 }), 600_000, 'Processing the module');
      const line = findVeilModules(text).find(m => m.name === 'CheckedElsewhere')?.genExecutableLine;
      assert.ok(line !== undefined);
      // The whole line, as the extension asks: Lean answers with the command that ends at the end of
      // the range or after it
      const lineEnd = text.split('\n')[line].length;
      const actionsFor = async (only?: string[]) => (await server.request('textDocument/codeAction', {
        textDocument: { uri },
        range: { start: { line, character: 0 }, end: { line, character: lineEnd } },
        context: { diagnostics: [], ...(only ? { only } : {}) },
      }) as { kind?: string; command?: { command: string; arguments: unknown[] } }[])
        .filter(action => action.kind === 'refactor.veil.modelCheckConfig');
      const [action] = await actionsFor(['refactor.veil.modelCheckConfig']);
      assert.strictEqual(action?.command?.command, 'veil.modelCheck.createConfig');
      assert.deepStrictEqual(action.command.arguments, [{
        import: 'VeilTest.Regression.ModelCheckBuildHelper',
        instantiation: [{ name: 'node', value: '_' }, { name: 'NodeSet', value: '_' }, { name: 'Buffer', value: '_' }],
        module: 'CheckedElsewhere',
        theory: [{ name: 'limit', value: '_' }],
      }, uri]);
      assert.deepStrictEqual(await actionsFor(), [], 'the menus of the editor do not show it');
    } finally {
      await server.close();
    }
  });

  test('Lean gives no import for a file outside the Lake libraries', async () => {
    const server = new LeanServer(repoRoot);
    try {
      await within(server.request('initialize',
        { processId: process.pid, rootUri: pathToFileURL(repoRoot).href, capabilities: {} }), 60_000, 'Starting Lean');
      server.notify('initialized', {});
      const file = path.join(repoRoot, fixture);
      const uri = pathToFileURL(file).href;
      const source = fs.readFileSync(file, 'utf8');
      const site = findVeilModules(source)[0];
      const text = source.split('\n').slice(0, site.endLine! + 1).join('\n');
      server.notify('textDocument/didOpen', { textDocument: { uri, languageId: 'lean4', version: 1, text } });
      await within(server.request('textDocument/waitForDiagnostics', { uri, version: 1 }), 600_000, 'Processing the module');
      const line = site.genExecutableLine!;
      const actions = await server.request('textDocument/codeAction', {
        textDocument: { uri },
        range: { start: { line, character: 0 }, end: { line, character: text.split('\n')[line].length } },
        context: { diagnostics: [], only: ['refactor.veil.modelCheckConfig'] },
      }) as { command?: { command: string; arguments: [ConfigTemplate, string] } }[];
      const action = actions.find(action => action.command?.command === 'veil.modelCheck.createConfig');
      assert.ok(action?.command);
      assert.deepStrictEqual(action.command.arguments, [{
        import: null,
        instantiation: [{ name: 'node', value: '_' }, { name: 'NodeSet', value: '_' }],
        module: 'RunnerFixture',
        theory: [{ name: 'limit', value: '_' }],
      }, uri]);
    } finally {
      await server.close();
    }
  });

  test('Lean says where the declarations of the module of a config are', async () => {
    const server = new LeanServer(repoRoot);
    try {
      await within(server.request('initialize',
        { processId: process.pid, rootUri: pathToFileURL(repoRoot).href, capabilities: {} }), 60_000, 'Starting Lean');
      server.notify('initialized', {});
      const file = path.join(repoRoot, fixture);
      const uri = pathToFileURL(file).href;
      const lines = fs.readFileSync(file, 'utf8').split('\n');
      // The module, and a config command for it, which builds as the first one of the fixture does
      const moduleEnd = findVeilModules(lines.join('\n'))[0].endLine!;
      const command = '#model_check_build RunnerFixture { node := Fin 2, NodeSet := _ } { limit := 2 }';
      const text = [...lines.slice(0, moduleEnd + 1), '', command].join('\n');
      server.notify('textDocument/didOpen', { textDocument: { uri, languageId: 'lean4', version: 1, text } });
      await within(server.request('textDocument/waitForDiagnostics', { uri, version: 1 }), 600_000, 'Processing the config');
      const line = moduleEnd + 2;
      const actions = await server.request('textDocument/codeAction', {
        textDocument: { uri },
        range: { start: { line, character: 0 }, end: { line, character: command.length } },
        context: { diagnostics: [], only: ['refactor.veil.modelCheckSources'] },
      }) as { command?: { command: string; arguments: [ModuleSources] } }[];
      const sources = actions.find(action => action.command?.command === 'veil.modelCheck.sources')?.command?.arguments[0];
      assert.ok(sources);
      const lineOf = (start: string) => lines.findIndex(l => l.startsWith(start));
      const expected = (name: string, start: string) => ({ name, file, line: lineOf(start), character: 0 });
      assert.deepStrictEqual(sources, {
        actions: [expected('after_init', 'after_init'), expected('finish', 'action finish '),
          expected('finishAfter', 'action finishAfter'), expected('reset', 'action reset')],
        properties: [expected('bounded', 'invariant [bounded]')],
      });
    } finally {
      await server.close();
    }
  });

  test('unfinished configs report their input holes without compiling a broken main', () => {
    const cases = [
      {
        command: '#model_check_build CheckedElsewhere { node := Fin 2, NodeSet := _, Buffer := _ } { limit := _ }',
        hole: 'limit := _',
        messages: ["don't know how to synthesize placeholder"],
        goal: '⊢ Nat',
      },
      {
        command: '#model_check_build CheckedElsewhere { node := _, NodeSet := _, Buffer := _ } { limit := 2 }',
        hole: 'node := _',
        messages: ["don't know how to synthesize placeholder", 'typeclass instance problem is stuck'],
        goal: '⊢ Type',
      },
      {
        command: '#model_check_build CheckedElsewhere { node := Fin 2, NodeSet := _, Buffer := _ } _',
        hole: '} _',
        messages: ["don't know how to synthesize placeholder"],
        goal: '⊢ Theory',
      },
      {
        command: '#model_check_build CheckedElsewhere _ { limit := true }',
        hole: 'CheckedElsewhere _',
        messages: ["don't know how to synthesize placeholder", 'Type mismatch'],
        goal: '⊢ Instantiation',
      },
    ];
    const header = 'module\n\npublic import Veil\npublic import VeilTest.Regression.ModelCheckBuildHelper\n\n';
    const source = header + cases.map(item => item.command).join('\n');
    const lean = spawnSync('lake', ['env', 'lean', '--json', '--stdin'],
      { cwd: repoRoot, input: source, encoding: 'utf8', maxBuffer: 4 * 1024 * 1024 });
    if (lean.error) throw lean.error;
    assert.strictEqual(lean.status, 1);
    assert.doesNotMatch(lean.stdout + lean.stderr, /PANIC|Compilation failed|declaration has metavariables/);
    const errors = lean.stdout.split('\n').filter(line => line.startsWith('{'))
      .map(line => JSON.parse(line) as { severity: string; data: string; pos: { line: number; column: number }; endPos: { column: number } })
      .filter(message => message.severity === 'error');
    assert.strictEqual(errors.length, cases.reduce((total, item) => total + item.messages.length, 0), lean.stdout);
    cases.forEach(item => {
      const line = source.split('\n').indexOf(item.command) + 1;
      const diagnostics = errors.filter(error => error.pos.line === line);
      assert.strictEqual(diagnostics.length, item.messages.length, lean.stdout);
      item.messages.forEach((message, index) => {
        assert.ok(diagnostics[index].data.startsWith(message), diagnostics[index].data);
      });
      assert.ok(diagnostics[0].data.includes(item.goal), diagnostics[0].data);
      const column = item.command.indexOf(item.hole) + item.hole.length - 1;
      assert.deepStrictEqual(diagnostics[0].pos, { line, column });
      assert.strictEqual(diagnostics[0].endPos.column, column + 1);
    });
  });

  test('a binary that cannot run fails', async () => {
    const outcome = await new CheckerRun({ binary: path.join(repoRoot, 'no-such-binary'), args: [] }).outcome;
    assert.strictEqual(outcome.kind, 'failed');
  });
}

async function main(): Promise<void> {
  let failures = 0;
  for (const { name, run } of tests) {
    try {
      await run();
      console.log(`ok   ${name}`);
    } catch (e) {
      failures++;
      console.log(`FAIL ${name}\n${e instanceof Error ? e.stack : e}`);
    }
  }
  console.log(failures === 0 ? `All ${tests.length} tests passed` : `${failures} of ${tests.length} tests failed`);
  process.exit(failures === 0 ? 0 : 1);
}

void main();
