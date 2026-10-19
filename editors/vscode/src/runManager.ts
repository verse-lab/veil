import * as os from 'os';
import * as path from 'path';
import * as vscode from 'vscode';
import { describeResult } from './protocol';
import { ResultStore, RunSource } from './resultStore';
import { CheckerRun, parallelArgs } from './runner';
import { ModuleSources, RunSnapshot, recordHistory } from './snapshot';

/** A `#model_check_build` command whose binary is ready. */
export interface RunTarget {
  uri: vscode.Uri;
  line: number;
  module: string;
  /** As `BuildCommandSite.command` */
  command: string;
  binary: string;
  /** The arguments of the binary, if the user chose them for this run, instead of the settings */
  args?: string[];
  /** Where the actions and properties of the module are */
  sources?: ModuleSources;
}

export function sourceOf(target: RunTarget): RunSource {
  return { file: target.uri.toString(), command: target.command };
}

function clock(): string {
  return new Date().toLocaleTimeString();
}

/** Runs one model checker at a time, as TLC's extension does, keeps the last run to show, and saves
 * each run once it ends. */
export class RunManager implements vscode.Disposable {
  private run: CheckerRun | undefined;
  private target: RunTarget | undefined;
  private current: RunSnapshot | undefined;
  private readonly statusChanged = new vscode.EventEmitter<void>();
  private readonly progressed = new vscode.EventEmitter<void>();
  /** Fires when a run starts, is being stopped, or ends */
  readonly onDidChangeStatus = this.statusChanged.event;
  /** Fires when the running binary reports progress */
  readonly onDidProgress = this.progressed.event;

  constructor(private readonly output: vscode.OutputChannel, private readonly store: ResultStore) {}

  /** The current run, or else the last one */
  get snapshot(): RunSnapshot | undefined {
    return this.current;
  }

  get lastTarget(): RunTarget | undefined {
    return this.target;
  }

  get isRunning(): boolean {
    return this.run !== undefined;
  }

  isRunningBinary(binary: string): boolean {
    return this.run !== undefined && this.target?.binary === binary;
  }

  start(target: RunTarget): void {
    if (this.run) throw new Error('A model check is already running');
    const config = vscode.workspace.getConfiguration('veil.modelChecker');
    const args = target.args ?? parallelArgs(config.get('workers', 0), config.get('thresholdToParallel', 20),
      config.get('numSubSteps', 1), os.cpus().length);
    const snapshot: RunSnapshot = {
      module: target.module,
      source: `${path.basename(target.uri.fsPath)}:${target.line + 1}`,
      binary: target.binary,
      args,
      status: 'running',
      startedAt: Date.now(),
      sources: target.sources,
      history: [],
    };
    this.output.clear();
    this.output.appendLine(`[${clock()}] ${[target.binary, ...args].join(' ')}`);
    const run = new CheckerRun({ binary: target.binary, args, cwd: path.dirname(target.uri.fsPath) }, {
      onStart: report => {
        snapshot.actionLabels = report.actionLabels;
        this.progressed.fire();
      },
      onProgress: progress => {
        snapshot.progress = progress;
        recordHistory(snapshot.history, progress);
        this.progressed.fire();
      },
      onOutput: line => this.output.appendLine(line),
    });
    this.run = run;
    this.target = target;
    this.current = snapshot;
    void run.outcome.then(outcome => {
      snapshot.endedAt = Date.now();
      switch (outcome.kind) {
        case 'finished':
          snapshot.status = 'finished';
          snapshot.result = outcome.result;
          this.output.appendLine(`[${clock()}] ${describeResult(outcome.result).text}`);
          break;
        case 'stopped':
          snapshot.status = 'stopped';
          this.output.appendLine(`[${clock()}] Stopped`);
          break;
        case 'failed':
          snapshot.status = 'failed';
          snapshot.error = outcome.message;
          this.output.appendLine(`[${clock()}] ${outcome.message}`);
          break;
      }
      this.run = undefined;
      this.store.save(sourceOf(target), snapshot).catch(err =>
        this.output.appendLine(`Could not save the result: ${err instanceof Error ? err.message : err}`));
      this.statusChanged.fire();
    });
    this.statusChanged.fire();
  }

  stop(): void {
    if (!this.run || !this.current) return;
    this.current.status = 'stopping';
    this.run.stop();
    this.statusChanged.fire();
  }

  dispose(): void {
    this.run?.stop();
    this.statusChanged.dispose();
    this.progressed.dispose();
  }
}
