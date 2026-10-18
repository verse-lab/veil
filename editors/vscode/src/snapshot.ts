// What the panel shows of a run, and the messages between the panel and the extension. This
// module is shared with the webview, so it must not import Node or VS Code modules.
import { Progress, modelCheckMetrics } from './protocol';

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
  /** The last progress that the binary reported */
  progress?: Progress;
  history: HistoryPoint[];
  /** The result, once the status is `finished` */
  result?: unknown;
  /** Why the run failed, once the status is `failed` */
  error?: string;
}

/** The messages that the panel sends to the extension. */
export type PanelMessage =
  | { type: 'ready' }
  | { type: 'stop' }
  | { type: 'runAgain' }
  | { type: 'showOutput' }
  | { type: 'openSource' };

/** The messages that the extension sends to the panel. */
export type ExtensionMessage = { type: 'state'; state: RunSnapshot | null };

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
