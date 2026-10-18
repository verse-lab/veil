// The output of a model checker binary. The formats are defined on the Lean side: see `runMain` and
// `StartReport` in `Veil/Core/Tools/ModelChecker/CompiledRuntime.lean`, and `Progress` in
// `Veil/Core/Tools/ModelChecker/Concrete/Progress.lean`. This module is shared with the webview, so
// it must not import Node or VS Code modules.

/** What a binary reports once, as `{"start": ...}` on the first line of stderr, before any progress. */
export interface StartReport {
  /** The labels of the actions of the module, without arguments, e.g. `Paxos.Label.send` */
  actionLabels: string[];
}

function parseObject(line: string): Record<string, unknown> | undefined {
  if (!line.startsWith('{')) return undefined;
  try {
    const json: unknown = JSON.parse(line);
    return typeof json === 'object' && json !== null ? json as Record<string, unknown> : undefined;
  } catch {
    return undefined;
  }
}

/** The start report on a line of stderr, if it is one. */
export function parseStartLine(line: string): StartReport | undefined {
  const start = parseObject(line)?.start;
  return typeof start === 'object' && start !== null ? start as StartReport : undefined;
}

/** A line of progress on stderr: the JSON of `Veil.ModelChecker.Concrete.Progress`. */
export interface Progress {
  status: string;
  isRunning: boolean;
  isCancelled: boolean;
  /** Since the binary started */
  elapsedMs: number;
  details: ProgressDetails;
}

export type ProgressDetails =
  | { modelCheck: { metrics: ModelCheckMetrics } }
  | { simulation: { metrics: SimulationMetrics } };

/** The counts of a model check, in TLC's terms. */
export interface ModelCheckMetrics {
  /** The BFS depth reached */
  diameter: number;
  /** The post-states generated, before deduplication */
  statesFound: number;
  distinctStates: number;
  /** The states found but not explored yet */
  queue: number;
  actionStats: ActionStat[];
  /** The labels of all actions, as in `StartReport`. Empty in the progress of a binary, which
   * reports them only once, when it starts. */
  allActionLabels: string[];
}

export interface ActionStat {
  /** The action and its arguments, e.g. `Paxos.Label.send 1 2` */
  name: string;
  statesGenerated: number;
  distinctStates: number;
}

export interface SimulationMetrics {
  tracesRun: number;
  numTraces: number;
}

/** The progress on a line of stderr, if it has any. */
export function parseProgressLine(line: string): Progress | undefined {
  const json = parseObject(line);
  return json && 'details' in json && 'elapsedMs' in json ? json as unknown as Progress : undefined;
}

export function modelCheckMetrics(progress: Progress): ModelCheckMetrics | undefined {
  return 'modelCheck' in progress.details ? progress.details.modelCheck.metrics : undefined;
}

export type VerdictKind = 'success' | 'violation' | 'cancelled' | 'error' | 'unknown';

export interface Verdict {
  kind: VerdictKind;
  text: string;
}

function show(value: unknown): string {
  return typeof value === 'string' ? value : JSON.stringify(value);
}

/** What a result says, worded as `TraceDisplay.formatModelCheckResult` words it in Lean. */
export function describeResult(result: unknown): Verdict {
  const r = (typeof result === 'object' && result !== null ? result : {}) as Record<string, unknown>;
  if (r.error !== undefined && r.error !== null) return { kind: 'error', text: `Error: ${show(r.error)}` };
  switch (r.result) {
    case 'found_violation': {
      const violation = (r.violation ?? {}) as Record<string, unknown>;
      const violates = Array.isArray(violation.violates) && violation.violates.length > 0
        ? ` (violates: ${violation.violates.map(show).join(', ')})`
        : '';
      return { kind: 'violation', text: `Violation: ${show(violation.kind)}${violates}` };
    }
    case 'no_violation_found':
      return { kind: 'success', text: `No violation (explored ${show(r.explored_states)} states)` };
    case 'cancelled':
      return { kind: 'cancelled', text: 'Cancelled' };
    default:
      return { kind: 'unknown', text: `Unknown result: ${show(r.result)}` };
  }
}
