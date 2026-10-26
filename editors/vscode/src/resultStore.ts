// The last run of each `#mc_config` command, kept on disk so that it outlives the window,
// and the files that runs are exported to. This module does not use VS Code, so that the tests can
// run it.
import { createHash } from 'crypto';
import { promises as fs } from 'fs';
import * as path from 'path';
import { BuildStatus } from './buildCommands';
import { RunOutcomeKind, RunSnapshot, describeRun } from './snapshot';

/** The version of the format of saved and exported runs. Files of other versions are not read. */
export const FORMAT_VERSION = 1;

/** The command that a run is of */
export interface RunSource {
  /** The URI of the file of the command */
  file: string;
  /** The text of the command, as `BuildCommandSite.command` */
  command: string;
}

/** A run as it is saved, and exported */
export interface SavedRun {
  formatVersion: number;
  /** Missing for a result that did not come from a run of the extension, e.g. one that a binary
   * printed on the command line */
  source?: RunSource;
  run: RunSnapshot;
}

/** What the index keeps of a saved run: enough for a lens, without reading the run */
export interface SavedRunSummary {
  source: RunSource;
  /** The binary that ran, as Lean reported it */
  binary: string;
  outcome: RunOutcomeKind;
  /** E.g. `No violation (explored 4 states)` */
  text: string;
  endedAt: number;
}

function isObject(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null;
}

/** Write `file` at once, so that a reader never sees it half written */
async function writeAtomically(file: string, data: string): Promise<void> {
  const tmp = `${file}.tmp`;
  await fs.writeFile(tmp, data);
  await fs.rename(tmp, file);
}

/** The runs saved in a directory: a file per run, and an index of them. */
export class ResultStore {
  private readonly summaries = new Map<string, SavedRunSummary>();
  /** The writes to the directory, one after the other */
  private writes: Promise<void> = Promise.resolve();

  /** Read the current limit on each save; saving more removes the oldest runs. */
  constructor(private readonly dir: string, private readonly getLimit: () => number = () => 50) {}

  private static key(source: RunSource): string {
    return createHash('sha256').update(`${source.file}\n${source.command}`).digest('hex').slice(0, 24);
  }

  private get indexFile(): string {
    return path.join(this.dir, 'index.json');
  }

  private runFile(key: string): string {
    return path.join(this.dir, `${key}.json`);
  }

  /** Read the index. A missing or unreadable index is an empty one. */
  async load(): Promise<void> {
    try {
      const index: unknown = JSON.parse(await fs.readFile(this.indexFile, 'utf8'));
      if (!isObject(index) || index.formatVersion !== FORMAT_VERSION || !Array.isArray(index.runs)) return;
      for (const summary of index.runs as SavedRunSummary[]) this.summaries.set(ResultStore.key(summary.source), summary);
    } catch {
      // Nothing was saved yet
    }
  }

  summary(source: RunSource): SavedRunSummary | undefined {
    return this.summaries.get(ResultStore.key(source));
  }

  /** The summary of the run saved last */
  newest(): SavedRunSummary | undefined {
    let newest: SavedRunSummary | undefined;
    for (const summary of this.summaries.values()) if (!newest || summary.endedAt > newest.endedAt) newest = summary;
    return newest;
  }

  /** Save `run`, which has ended, as the last run of `source`. The summaries change at once, and the
   * files once the returned promise resolves. */
  save(source: RunSource, run: RunSnapshot): Promise<void> {
    const key = ResultStore.key(source);
    const { kind, text } = describeRun(run);
    this.summaries.set(key, { source, binary: run.binary, outcome: kind, text, endedAt: run.endedAt ?? Date.now() });
    const configuredLimit = this.getLimit();
    // Settings edited as JSON can bypass VS Code's validation.
    const limit = Number.isInteger(configuredLimit) && configuredLimit >= 1 ? configuredLimit : 50;
    const removed = [...this.summaries.entries()]
      .sort(([, a], [, b]) => b.endedAt - a.endedAt)
      .slice(limit)
      .map(([k]) => k);
    for (const k of removed) this.summaries.delete(k);
    const saved: SavedRun = { formatVersion: FORMAT_VERSION, source, run };
    const data = JSON.stringify(saved);
    const index = JSON.stringify({ formatVersion: FORMAT_VERSION, runs: [...this.summaries.values()] });
    this.writes = this.writes.catch(() => {}).then(async () => {
      await fs.mkdir(this.dir, { recursive: true });
      await writeAtomically(this.runFile(key), data);
      for (const k of removed) await fs.rm(this.runFile(k), { force: true });
      await writeAtomically(this.indexFile, index);
    });
    return this.writes;
  }

  /** The saved run of `source`, if it is still there */
  async read(source: RunSource): Promise<SavedRun | undefined> {
    try {
      const saved = parseRunFile(await fs.readFile(this.runFile(ResultStore.key(source)), 'utf8'), '', 0);
      return saved?.source ? saved : undefined;
    } catch {
      return undefined;
    }
  }
}

/** Whether a saved run is of the binary that Lean builds for its command now, unknown until Lean
 * has built one. The name of a binary has a hash of the code that it was built from, so another name
 * means that the model checker has changed, e.g. because the model did. Only the name counts, so that
 * runs exported on another machine compare too. A saved run is also outdated once Lean reports that
 * the imports of its file have changed since Lean read them, e.g. because the model was saved: Lean
 * builds from the old imports until the file is restarted.
 *
 * The hash covers the C code emitted for the command and the names of its imports, not the compiled
 * imports: a change to code that the model checker only links against goes unnoticed. */
export type Freshness = 'current' | 'outdated' | 'unknown';

export function freshness(savedBinary: string, status: BuildStatus, importsOutOfDate = false): Freshness {
  // No binary, e.g. for a result that a binary printed on the command line
  if (!savedBinary) return 'unknown';
  if (importsOutOfDate) return 'outdated';
  if (status.kind !== 'built') return 'unknown';
  return path.basename(status.binary) === path.basename(savedBinary) ? 'current' : 'outdated';
}

/** The run in a file that the user opens: one that was exported, or the result that a binary printed,
 * as a run that finished when the file was last modified. Anything else is `undefined`. */
export function parseRunFile(text: string, fileName: string, modifiedAt: number): SavedRun | undefined {
  let json: unknown;
  try {
    json = JSON.parse(text);
  } catch {
    return undefined;
  }
  if (!isObject(json)) return undefined;
  if (json.formatVersion === FORMAT_VERSION && isObject(json.run)) return json as unknown as SavedRun;
  if (!('result' in json) && !('error' in json)) return undefined;
  const name = path.basename(fileName);
  return {
    formatVersion: FORMAT_VERSION,
    run: {
      module: name, source: name, binary: '', args: [], status: 'finished',
      startedAt: modifiedAt, endedAt: modifiedAt, history: [], result: json,
    },
  };
}
