// The tests of the parts of the extension that do not use VS Code: `npm test`. The tests with
// binaries first build those of `fixtures/RunnerFixture.lean` with Lean, which needs `lake` and a
// built Veil. Set VEIL_SKIP_BINARY_TESTS=1 to skip them.
import * as assert from 'assert';
import { spawnSync } from 'child_process';
import * as fs from 'fs';
import * as path from 'path';
import * as React from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { BUILT_PREFIX, ReportedMessage, Severity, buildStatus, findBuildCommands } from '../src/buildCommands';
import { Progress, StartReport, describeResult, modelCheckMetrics, parseProgressLine, parseStartLine } from '../src/protocol';
import { CheckerRun, parallelArgs } from '../src/runner';
import { HistoryPoint, RunSnapshot, recordHistory } from '../src/snapshot';
import { NoRun, RunView } from '../webview/view';

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
    { line: 1, character: 0, endLine: 3, module: 'Foo' },
    { line: 4, character: 2, endLine: 4, module: 'Bar.Baz' },
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

// ---- Build status ----

const site = { line: 1, character: 0, endLine: 3, module: 'Foo' };
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
      actionStats: [{ distinctStates, name: 'M.Label.finish 0', statesGenerated: distinctStates }],
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
  const line = '{"start":{"actionLabels":["M.Label.finish","M.Label.reset"]}}';
  assert.deepStrictEqual(parseStartLine(line), { actionLabels: ['M.Label.finish', 'M.Label.reset'] });
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
      allActionLabels: ['Paxos.Label.send', 'Paxos.Label.decide', 'Paxos.Label.prepare'],
      actionStats: [
        { name: 'Paxos.Label.send 0 1', statesGenerated: 10, distinctStates: 5 },
        { name: 'Paxos.Label.send 1 0', statesGenerated: 4, distinctStates: 2 },
        { name: 'Paxos.Label.decide', statesGenerated: 0, distinctStates: 0 },
      ],
    } } },
  };
  assertShows(render(snapshot({ progress, history: [point(0), point(1000)] })), [
    'Paxos', 'MCPaxos.lean:12', 'Running...', 'Stop', '8 workers', 'Diameter:', '123,456', '65,432',
    'Elapsed time:', '1m 3.0s', 'Metrics History (2 samples, 1.0s)', 'Graph', 'Table', 'Copy JSON',
    'States Found', 'Queue Size', '<path class="chart-line"', 'Action Coverage (2 actions',
    '2 never enabled', 'Never enabled: decide, prepare', 'send', '0 1',
  ]);
});

test('the panel sorts multiple action arguments numerically', () => {
  const progress = parseProgressLine(progressLine(1, 1))!;
  modelCheckMetrics(progress)!.actionStats = ['10 1', '2 10', '2 2', '1 10'].map(args => ({
    name: `M.Label.finishAfter ${args}`, statesGenerated: 1, distinctStates: 1,
  }));
  const html = render(snapshot({ progress }));
  const variants = ['1 10', '2 2', '2 10', '10 1'].map(args => `<span>${args}</span>`);
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
      assert.deepStrictEqual(start?.actionLabels,
        ['RunnerFixture.Label.finish', 'RunnerFixture.Label.finishAfter', 'RunnerFixture.Label.reset']);
      assert.deepStrictEqual(progress && modelCheckMetrics(progress)?.allActionLabels, []);
      assertShows(render(snapshot({ progress, actionLabels: start?.actionLabels })),
        ['Never enabled: reset', 'finishAfter', '<span>0 1</span>', '<span>1 0</span>']);
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
