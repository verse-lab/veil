// The view of the panel. Its layout follows the progress viewer of the Lean infoview
// (`Veil/Core/UI/Widget/ProgressViewer.lean`), under a header like that of TLC's extension. It
// does not use the webview API, so that the tests can render it.
import ModelCheckerView from '@veil/widget/traceDisplay';
import { OpenSource, OpenSourceContext, SourceLink, formatValue, logicalCtor } from '@veil/widget/veilUtils';
import * as React from 'react';
import { ActionStat, VerdictKind, describeResult, modelCheckMetrics } from '../src/protocol';
import { HistoryPoint, ModuleSources, PanelMessage, RunOrigin, RunSnapshot } from '../src/snapshot';
import { CHART_CSS, MetricChart } from './chart';

/** Sends a message to the extension */
export const Send = React.createContext<(message: PanelMessage) => void>(() => {});

/** E.g. `6.2s`, `1m 3.4s` or `2h 5m 3s`, as `formatElapsedTime` in Lean */
function formatElapsed(ms: number): string {
  const seconds = Math.floor(ms / 1000);
  const h = Math.floor(seconds / 3600);
  const m = Math.floor((seconds % 3600) / 60);
  const s = seconds % 60;
  const tenths = Math.floor((ms % 1000) / 100);
  if (h > 0) return `${h}h ${m}m ${s}s`;
  if (m > 0) return `${m}m ${s}.${tenths}s`;
  return `${s}.${tenths}s`;
}

/** E.g. `00:01:03`, as TLC shows times */
function formatHMS(ms: number): string {
  const seconds = Math.floor(ms / 1000);
  const pad = (n: number) => String(n).padStart(2, '0');
  return `${pad(Math.floor(seconds / 3600))}:${pad(Math.floor((seconds % 3600) / 60))}:${pad(seconds % 60)}`;
}

const count = (n: number) => n.toLocaleString('en-US');

/** The time, with the date for another day than today, which a saved run can be from */
function clock(epochMs: number): string {
  const date = new Date(epochMs);
  return date.toDateString() === new Date().toDateString() ? date.toLocaleTimeString() : date.toLocaleString();
}

const verdictClass: Record<VerdictKind, string> = {
  success: 'success',
  violation: 'error',
  cancelled: 'warning',
  error: 'error',
  unknown: 'warning',
};

/** Why a run is outdated, as `freshness` tells */
const OUTDATED_BECAUSE = 'the model or the config has changed since this run';

export interface RunViewProps {
  run: RunSnapshot;
  now: number;
  /** Where the run comes from, see `PanelState` */
  origin?: RunOrigin;
  fileName?: string;
  canRunAgain?: boolean;
  outdated?: boolean;
}

/** Opens the sources of the actions and properties of `sources` */
function sourceOpener(sources: ModuleSources | undefined, send: (message: PanelMessage) => void): OpenSource | undefined {
  if (!sources) return undefined;
  return (kind, name) => {
    const location = (kind === 'action' ? sources.actions : sources.properties).find(source => source.name === name);
    return location && (() => send({ type: 'openLocation', location }));
  };
}

export function RunView(props: RunViewProps) {
  const send = React.useContext(Send);
  const openSource = React.useMemo(() => sourceOpener(props.run.sources, send), [props.run.sources, send]);
  // The links of the trace and of the coverage to the module
  return <OpenSourceContext.Provider value={openSource}><RunContent {...props} /></OpenSourceContext.Provider>;
}

function RunContent({ run, now, origin = 'live', fileName, canRunAgain = true, outdated = false }: RunViewProps) {
  const send = React.useContext(Send);
  const active = run.status === 'running' || run.status === 'stopping';
  const metrics = run.progress && modelCheckMetrics(run.progress);
  // A binary reports the labels once, when it starts, rather than in its progress
  const labels = run.actionLabels ?? metrics?.allActionLabels ?? [];
  const elapsed = (run.endedAt ?? now) - run.startedAt;
  return <>
  <div className="run">
    <div className="header">
      <div>
        <span className="title">{run.module}</span>
        <a className="source" onClick={() => send({ type: 'openSource' })}>{run.source}</a>
      </div>
      <div className="actions">
        <button className="primary" disabled={active || !canRunAgain} onClick={() => send({ type: 'runAgain' })}>Check again</button>
        {!active && <button onClick={() => send({ type: 'export' })}>Export...</button>}
        {/* The output channel has the run of this window only */}
        {origin === 'live' && <button onClick={() => send({ type: 'showOutput' })}>Full output</button>}
      </div>
    </div>
    {origin !== 'live' && <div className={outdated ? 'origin outdated' : 'origin'}>
      {origin === 'file' ? `Opened from ${fileName}` : 'Saved result'}
      {outdated && ` · outdated: ${OUTDATED_BECAUSE}`}
    </div>}
    {origin === 'live' && outdated && <div className="origin outdated">Outdated: {OUTDATED_BECAUSE}</div>}
    <StatusLine run={run} />
    <div className="muted">
      Started {clock(run.startedAt)}{run.endedAt !== undefined && `, ended ${clock(run.endedAt)}`}
      {' · '}{run.args.length === 0 ? 'sequential' : `${run.args[0]} workers`}
    </div>
    <div className="mono">
      <table className="stats"><tbody>
        {metrics && <>
          <StatRow label="Diameter:" value={count(metrics.diameter)} />
          <StatRow label="States Found:" value={count(metrics.statesFound)} />
          <StatRow label="Distinct States:" value={count(metrics.distinctStates)} />
          <StatRow label="Queue:" value={count(metrics.queue)} />
        </>}
        <StatRow label="Elapsed time:" value={formatElapsed(elapsed)} />
      </tbody></table>
      {run.history.length >= 2 && <MetricsHistory history={run.history} />}
      {metrics && (metrics.actionStats.length > 0 || labels.length > 0)
        && <ActionCoverage stats={metrics.actionStats} labels={labels} />}
    </div>
    {run.status === 'failed' && <pre className="error-box">{run.error}</pre>}
  </div>
  {run.status === 'finished' && <Result result={run.result} />}
  </>;
}

function StatusLine({ run }: { run: RunSnapshot }) {
  const send = React.useContext(Send);
  switch (run.status) {
    case 'running':
      return <div className="status running">
        <i>{run.progress?.status ?? 'Starting...'}</i>
        <button onClick={() => send({ type: 'stop' })}>Stop</button>
      </div>;
    case 'stopping':
      return <div className="status running"><i>Stopping...</i></div>;
    case 'stopped':
      return <div className="status warning">Stopped</div>;
    case 'failed':
      return <div className="status error">Failed</div>;
    case 'finished':
      // As in Lean, the result below gives the verdict
      return <div className={`status ${verdictClass[describeResult(run.result).kind]}`}>Done!</div>;
  }
}

function StatRow({ label, value }: { label: string; value: string }) {
  return <tr><td>{label}</td><td className="num">{value}</td></tr>;
}

const METRICS: { key: Exclude<keyof HistoryPoint, 'timeMs'>; title: string }[] = [
  { key: 'diameter', title: 'Diameter' },
  { key: 'statesFound', title: 'States Found' },
  { key: 'distinctStates', title: 'Distinct States' },
  { key: 'queue', title: 'Queue Size' },
];

/** The history as JSON, in the format of the infoview's "Copy JSON" */
function historyJson(history: HistoryPoint[]): string {
  return JSON.stringify(history.map(({ timeMs, diameter, statesFound, distinctStates, queue }) =>
    ({ timeMs, timeStr: formatHMS(timeMs), diameter, statesFound, distinctStates, queue })));
}

/** The history as charts, or as TLC's table of states, as in the infoview */
function MetricsHistory({ history }: { history: HistoryPoint[] }) {
  const [view, setView] = React.useState<'graph' | 'table'>('graph');
  const [copied, setCopied] = React.useState(false);
  const copy = () => void navigator.clipboard.writeText(historyJson(history)).then(() => {
    setCopied(true);
    setTimeout(() => setCopied(false), 2000);
  });
  const span = history[history.length - 1].timeMs - history[0].timeMs;
  return <details>
    <summary>Metrics History ({history.length} samples, {formatElapsed(span)})</summary>
    <div className="history-toolbar">
      <div className="toggle">
        <button className={view === 'graph' ? 'primary' : ''} onClick={() => setView('graph')}>Graph</button>
        <button className={view === 'table' ? 'primary' : ''} onClick={() => setView('table')}>Table</button>
      </div>
      <button onClick={copy}>{copied ? 'Copied!' : 'Copy JSON'}</button>
    </div>
    {view === 'graph'
      ? <div className="charts">
          {METRICS.map(({ key, title }) => <MetricChart key={key} title={title}
            points={history.map(point => ({ timeMs: point.timeMs, value: point[key] }))} />)}
        </div>
      : <div className="scroll">
          <table className="history">
            <thead><tr><th>Time</th><th>Diameter</th><th>Found</th><th>Distinct</th><th>Queue</th></tr></thead>
            <tbody>
              {history.map((point, i) => <tr key={i}>
                <td>{formatHMS(point.timeMs)}</td>
                <td>{count(point.diameter)}</td>
                <td>{count(point.statesFound)}</td>
                <td>{count(point.distinctStates)}</td>
                <td>{count(point.queue)}</td>
              </tr>)}
            </tbody>
          </table>
        </div>}
  </details>;
}

interface ActionGroup {
  name: string;
  generated: number;
  distinct: number;
  variants: { args: string; generated: number; distinct: number }[];
}

/** A constructor's name and displayed arguments, as in `actionAndArgs` of the infoview. */
function actionAndArgs(label: unknown): [string, string] {
  const ctor = logicalCtor(label);
  if (!ctor) return [formatValue(label), ''];
  return [ctor.name, ctor.args.map(([name, value]) =>
    name === undefined ? formatValue(value) : `${name}=${formatValue(value)}`).join(', ')];
}

function groupActions(stats: ActionStat[]): ActionGroup[] {
  const groups = new Map<string, ActionGroup>();
  for (const stat of stats) {
    const [name, args] = actionAndArgs(stat.label);
    const group = groups.get(name) ?? { name, generated: 0, distinct: 0, variants: [] };
    group.generated += stat.statesGenerated;
    group.distinct += stat.distinctStates;
    group.variants.push({ args, generated: stat.statesGenerated, distinct: stat.distinctStates });
    groups.set(name, group);
  }
  const sorted = [...groups.values()].sort((a, b) => a.name.localeCompare(b.name));
  for (const group of sorted) group.variants.sort((a, b) => a.args.localeCompare(b.args, 'en', { numeric: true }));
  return sorted;
}

function coverageClass(generated: number, variant = false): string {
  return `coverage-row${generated === 0 ? ' never' : ''}${variant ? ' variant' : ''}`;
}

/** `labels` are those of all actions, so that the actions that are missing from `stats` show as
 * never enabled, as in `getNeverEnabledActions` of the infoview */
function ActionCoverage({ stats, labels }: { stats: ActionStat[]; labels: string[] }) {
  const groups = groupActions(stats);
  const missing = labels.filter(name => !groups.some(group => group.name === name));
  const never = [...groups.filter(group => group.generated === 0).map(group => group.name), ...missing].sort();
  return <details>
    <summary>
      Action Coverage ({groups.length} actions
      {never.length > 0 && <span className="warning"> — {never.length} never enabled ⚠</span>})
    </summary>
    <div className="coverage">
      <div className="coverage-row heading"><span>Action</span><span>Generated</span><span>Distinct</span></div>
      {groups.map(group => {
        const cells = <>
          <span><SourceLink kind="action" name={group.name}>{group.name}</SourceLink></span>
          <span className="num">{count(group.generated)}</span>
          <span className="num">{count(group.distinct)}</span>
        </>;
        if (group.variants.length === 1) return <div key={group.name} className={coverageClass(group.generated)}>{cells}</div>;
        return <details key={group.name}>
          <summary className={`${coverageClass(group.generated)} expandable`}>{cells}</summary>
          {group.variants.map(variant => <div key={variant.args} className={coverageClass(variant.generated, true)}>
            <span>{variant.args || '(no args)'}</span>
            <span className="num">{count(variant.generated)}</span>
            <span className="num">{count(variant.distinct)}</span>
          </div>)}
        </details>;
      })}
      {never.length > 0 && <div className="never-warning">⚠ Never enabled: {never.join(', ')}</div>}
    </div>
  </details>;
}

/** The result of a finished run, as `mkFinalResultHtml` shows it in Lean */
function Result({ result }: { result: unknown }) {
  const fields = typeof result === 'object' && result !== null ? result as Record<string, unknown> : {};
  if (fields.error !== undefined && fields.error !== null) return <pre className="error-box">{String(fields.error)}</pre>;
  if (Object.keys(fields).length === 0) return <p className="warning"><i>No result data available</i></p>;
  return <div className="result"><ModelCheckerView result={result} layout="vertical" kind="modelCheck" /></div>;
}

export function NoRun() {
  return <p className="muted">
    No model check has run yet. Run one with the “Run model checker” lens above
    a <code>#mc_config</code> command.
  </p>;
}

export const CSS = `
body {
  color: var(--vscode-foreground);
  background: var(--vscode-editor-background);
  font-family: var(--vscode-font-family);
  font-size: var(--vscode-font-size);
  padding: 0 16px 16px;
}
.muted { color: var(--vscode-descriptionForeground); }
.mono { font-family: var(--vscode-editor-font-family); font-size: 12px; margin-top: 8px; }
.run .header { display: flex; flex-wrap: wrap; justify-content: space-between; align-items: center; gap: 8px; margin-top: 12px; }
.title { font-size: 1.3em; font-weight: bold; margin-right: 8px; }
.source { color: var(--vscode-textLink-foreground); cursor: pointer; }
.actions { display: flex; gap: 6px; }
.run button {
  color: var(--vscode-button-secondaryForeground);
  background: var(--vscode-button-secondaryBackground);
  border: none; border-radius: 2px; padding: 3px 10px; cursor: pointer; font-family: inherit;
}
.run button:hover:not(:disabled) { background: var(--vscode-button-secondaryHoverBackground); }
.run button:disabled { opacity: 0.5; cursor: default; }
.run button.primary { color: var(--vscode-button-foreground); background: var(--vscode-button-background); }
.run button.primary:hover:not(:disabled) { background: var(--vscode-button-hoverBackground); }
.status { margin: 10px 0 4px; font-weight: bold; display: flex; align-items: center; gap: 12px; }
.status.running { color: var(--vscode-charts-blue, #3794ff); font-weight: normal; }
.status.success { color: var(--vscode-testing-iconPassed, #3fb950); }
.status.error { color: var(--vscode-errorForeground); }
.status.warning, .warning { color: var(--vscode-editorWarning-foreground, #cc6600); }
.run table.stats { border-collapse: collapse; }
.run table.stats td { padding: 1px 12px 1px 0; }
.num { text-align: right; }
.run details { margin-top: 8px; }
.run summary { cursor: pointer; color: var(--vscode-descriptionForeground); }
.scroll { max-height: 300px; overflow: auto; margin-top: 4px; }
.run table.history { border-collapse: collapse; width: 100%; }
.run table.history th, .run table.history td { padding: 2px 8px; text-align: right; border-bottom: 1px solid var(--vscode-panel-border); }
.run table.history th { position: sticky; top: 0; background: var(--vscode-editor-background); }
.coverage { margin-top: 4px; }
.coverage details { margin-top: 0; }
.coverage-row { display: grid; grid-template-columns: 1fr 80px 70px; gap: 8px; padding: 1px 0; color: var(--vscode-foreground); }
.coverage-row.heading { font-weight: bold; border-bottom: 1px solid var(--vscode-panel-border); margin-bottom: 2px; }
.coverage-row.expandable span:first-child::before { content: '▸ '; }
.coverage details[open] > .coverage-row.expandable span:first-child::before { content: '▾ '; }
.coverage-row.variant { color: var(--vscode-descriptionForeground); }
.coverage-row.variant span:first-child { padding-left: 16px; }
.coverage-row.never { background: var(--vscode-inputValidation-warningBackground, rgba(204, 102, 0, 0.25)); }
.never-warning { margin-top: 6px; color: var(--vscode-editorWarning-foreground, #cc6600); }
.error-box {
  white-space: pre-wrap; word-break: break-word; padding: 8px; margin-top: 8px;
  border: 1px solid var(--vscode-inputValidation-errorBorder);
  background: var(--vscode-inputValidation-errorBackground);
}
.result { margin-top: 12px; }
.origin { margin-top: 4px; font-style: italic; color: var(--vscode-descriptionForeground); }
.origin.outdated { color: var(--vscode-editorWarning-foreground, #cc6600); }
.history-toolbar { display: flex; justify-content: space-between; margin: 6px 0 8px; }
.toggle { display: flex; gap: 4px; }
.charts { max-width: 720px; }
${CHART_CSS}`;
