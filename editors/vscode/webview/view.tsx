// The view of the panel. Its layout follows the progress viewer of the Lean infoview
// (`Veil/Core/UI/Widget/ProgressViewer.lean`), under a header like that of TLC's extension. It
// does not use the webview API, so that the tests can render it.
import * as React from 'react';
import { ActionStat, VerdictKind, describeResult, modelCheckMetrics } from '../src/protocol';
import { HistoryPoint, PanelMessage, RunSnapshot } from '../src/snapshot';

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
const clock = (epochMs: number) => new Date(epochMs).toLocaleTimeString();

const verdictClass: Record<VerdictKind, string> = {
  success: 'success',
  violation: 'error',
  cancelled: 'warning',
  error: 'error',
  unknown: 'warning',
};

export function RunView({ run, now }: { run: RunSnapshot; now: number }) {
  const send = React.useContext(Send);
  const active = run.status === 'running' || run.status === 'stopping';
  const metrics = run.progress && modelCheckMetrics(run.progress);
  const elapsed = (run.endedAt ?? now) - run.startedAt;
  return <div>
    <div className="header">
      <div>
        <span className="title">{run.module}</span>
        <a className="source" onClick={() => send({ type: 'openSource' })}>{run.source}</a>
      </div>
      <div className="actions">
        <button className="primary" disabled={active} onClick={() => send({ type: 'runAgain' })}>Check again</button>
        <button onClick={() => send({ type: 'showOutput' })}>Full output</button>
      </div>
    </div>
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
      {metrics && metrics.actionStats.length > 0 && <ActionCoverage stats={metrics.actionStats} />}
    </div>
    {run.status === 'finished' && <ResultJson result={run.result} />}
    {run.status === 'failed' && <pre className="error-box">{run.error}</pre>}
  </div>;
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
    case 'finished': {
      const verdict = describeResult(run.result);
      return <div className={`status ${verdictClass[verdict.kind]}`}>{verdict.text}</div>;
    }
  }
}

function StatRow({ label, value }: { label: string; value: string }) {
  return <tr><td>{label}</td><td className="num">{value}</td></tr>;
}

function MetricsHistory({ history }: { history: HistoryPoint[] }) {
  const span = history[history.length - 1].timeMs - history[0].timeMs;
  return <details>
    <summary>Metrics History ({history.length} samples, {formatElapsed(span)})</summary>
    <div className="scroll">
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
    </div>
  </details>;
}

interface ActionGroup {
  name: string;
  generated: number;
  distinct: number;
  variants: { args: string; generated: number; distinct: number }[];
}

/** `Paxos.Label.send 1 2` is action `send` with arguments `1 2` */
function splitAction(label: string): [string, string] {
  const space = label.indexOf(' ');
  const qualified = space < 0 ? label : label.slice(0, space);
  const args = space < 0 ? '' : label.slice(space + 1);
  const marker = '.Label.';
  const at = qualified.lastIndexOf(marker);
  return [at < 0 ? qualified : qualified.slice(at + marker.length), args];
}

function groupActions(stats: ActionStat[]): ActionGroup[] {
  const groups = new Map<string, ActionGroup>();
  for (const stat of stats) {
    const [name, args] = splitAction(stat.name);
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

function ActionCoverage({ stats }: { stats: ActionStat[] }) {
  const groups = groupActions(stats);
  const never = groups.filter(group => group.generated === 0).map(group => group.name);
  return <details>
    <summary>
      Action Coverage ({groups.length} actions
      {never.length > 0 && <span className="warning"> — {never.length} never enabled ⚠</span>})
    </summary>
    <div className="coverage">
      <div className="coverage-row heading"><span>Action</span><span>Generated</span><span>Distinct</span></div>
      {groups.map(group => {
        const cells = <>
          <span>{group.name}</span>
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

function ResultJson({ result }: { result: unknown }) {
  const send = React.useContext(Send);
  const text = JSON.stringify(result, null, 2);
  return <details open={describeResult(result).kind === 'violation'}>
    <summary>Result</summary>
    <button className="copy" onClick={() => send({ type: 'copy', text })}>Copy JSON</button>
    <pre className="raw">{text}</pre>
  </details>;
}

export function NoRun() {
  return <p className="muted">
    No model check has run yet. Run one with the “Run model checker” lens above
    a <code>#model_check_build</code> command.
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
.header { display: flex; flex-wrap: wrap; justify-content: space-between; align-items: center; gap: 8px; margin-top: 12px; }
.title { font-size: 1.3em; font-weight: bold; margin-right: 8px; }
.source { color: var(--vscode-textLink-foreground); cursor: pointer; }
.actions { display: flex; gap: 6px; }
button {
  color: var(--vscode-button-secondaryForeground);
  background: var(--vscode-button-secondaryBackground);
  border: none; border-radius: 2px; padding: 3px 10px; cursor: pointer; font-family: inherit;
}
button:hover:not(:disabled) { background: var(--vscode-button-secondaryHoverBackground); }
button:disabled { opacity: 0.5; cursor: default; }
button.primary { color: var(--vscode-button-foreground); background: var(--vscode-button-background); }
button.primary:hover:not(:disabled) { background: var(--vscode-button-hoverBackground); }
.status { margin: 10px 0 4px; font-weight: bold; display: flex; align-items: center; gap: 12px; }
.status.running { color: var(--vscode-charts-blue, #3794ff); font-weight: normal; }
.status.success { color: var(--vscode-testing-iconPassed, #3fb950); }
.status.error { color: var(--vscode-errorForeground); }
.status.warning, .warning { color: var(--vscode-editorWarning-foreground, #cc6600); }
table.stats { border-collapse: collapse; }
table.stats td { padding: 1px 12px 1px 0; }
.num { text-align: right; }
details { margin-top: 8px; }
summary { cursor: pointer; color: var(--vscode-descriptionForeground); }
.scroll { max-height: 300px; overflow: auto; margin-top: 4px; }
table.history { border-collapse: collapse; width: 100%; }
table.history th, table.history td { padding: 2px 8px; text-align: right; border-bottom: 1px solid var(--vscode-panel-border); }
table.history th { position: sticky; top: 0; background: var(--vscode-editor-background); }
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
button.copy { margin: 6px 0; }
pre.raw {
  max-height: 400px; overflow: auto; margin: 0; padding: 8px;
  background: var(--vscode-textBlockQuote-background);
  font-family: var(--vscode-editor-font-family); font-size: 12px;
}
`;
