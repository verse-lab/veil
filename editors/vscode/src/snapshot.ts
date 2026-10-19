// What the panel shows of a run, and the messages between the panel and the extension. This
// module is shared with the webview, so it must not import Node or VS Code modules.
import { Progress, VerdictKind, describeResult, modelCheckMetrics } from './protocol';

export type RunStatus = 'running' | 'stopping' | 'finished' | 'stopped' | 'failed';

/** A row of the metrics history, as in TLC's table of states. */
export interface HistoryPoint {
  /** Since the binary started */
  timeMs: number;
  diameter: number;
  statesFound: number;
  distinctStates: number;
  queue: number;
}

/** Where a declaration of a module is, as Lean gives it: a file, and an LSP position in it */
export interface DeclSource {
  /** The name that results give it */
  name: string;
  file: string;
  line: number;
  character: number;
}

/** Where the declarations of the module of a run are: the JSON of `Veil.ModuleSources` */
export interface ModuleSources {
  actions: DeclSource[];
  properties: DeclSource[];
}

export interface RunSnapshot {
  /** The module that is checked */
  module: string;
  /** Where the `#model_check_build` command is, e.g. `MCPaxos.lean:12` */
  source: string;
  binary: string;
  args: string[];
  status: RunStatus;
  /** Wall-clock times, in ms since the epoch */
  startedAt: number;
  endedAt?: number;
  /** The labels of all actions, from the start report of the binary */
  actionLabels?: string[];
  /** Where the actions and properties of the module are, if Lean said when the run started */
  sources?: ModuleSources;
  /** The last progress that the binary reported */
  progress?: Progress;
  history: HistoryPoint[];
  /** The result, once the status is `finished` */
  result?: unknown;
  /** Why the run failed, once the status is `failed` */
  error?: string;
}

export type RunOutcomeKind = VerdictKind | 'running' | 'stopped' | 'failed';

/** What a run came to, in a few words, e.g. for the status bar */
export function describeRun(run: RunSnapshot): { kind: RunOutcomeKind; text: string } {
  switch (run.status) {
    case 'running':
    case 'stopping':
      return { kind: 'running', text: 'Running' };
    case 'stopped':
      return { kind: 'stopped', text: 'Stopped' };
    case 'failed':
      return { kind: 'failed', text: `Failed: ${(run.error ?? '').split('\n', 1)[0]}` };
    case 'finished':
      return describeResult(run.result);
  }
}

/** Where the run that the panel shows comes from: this window, the runs saved before, or a file
 * that the user opened */
export type RunOrigin = 'live' | 'saved' | 'file';

export interface PanelState {
  run: RunSnapshot;
  origin: RunOrigin;
  /** The name of the file, for a run from a file */
  fileName?: string;
  /** Whether "Check again" can run the command of the run */
  canRunAgain: boolean;
  /** Whether a saved run is of another binary than the one that Lean has built for its command now */
  outdated?: boolean;
}

/** The messages that the panel sends to the extension. */
export type PanelMessage =
  | { type: 'ready' }
  | { type: 'stop' }
  | { type: 'runAgain' }
  | { type: 'export' }
  | { type: 'showOutput' }
  | { type: 'openSource' }
  | { type: 'openLocation'; location: DeclSource };

/** The messages that the extension sends to the panel. */
export type ExtensionMessage = { type: 'state'; state: PanelState | null };

/** The history keeps a point at least every this many ms, and only the latest point in between */
const HISTORY_GAP_MS = 1000;
/** When the history grows past this, every second point is dropped */
const MAX_HISTORY = 1000;

/** Add `progress` to `history`, which keeps a point about every second. */
export function recordHistory(history: HistoryPoint[], progress: Progress): void {
  const metrics = modelCheckMetrics(progress);
  if (!metrics) return;
  const point: HistoryPoint = {
    timeMs: progress.elapsedMs,
    diameter: metrics.diameter,
    statesFound: metrics.statesFound,
    distinctStates: metrics.distinctStates,
    queue: metrics.queue,
  };
  // The last point stays only once it is a gap after the point before it
  const last = history[history.length - 1];
  const beforeLast = history[history.length - 2];
  if (last !== undefined && beforeLast !== undefined && last.timeMs - beforeLast.timeMs < HISTORY_GAP_MS) {
    history[history.length - 1] = point;
  } else {
    history.push(point);
  }
  if (history.length > MAX_HISTORY) {
    const last = history[history.length - 1];
    const thinned = history.filter((_, i) => i % 2 === 0);
    if (thinned[thinned.length - 1] !== last) thinned.push(last);
    history.splice(0, history.length, ...thinned);
  }
}
