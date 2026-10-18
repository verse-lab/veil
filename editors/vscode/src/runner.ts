// Runs model checker binaries. This module does not use VS Code, so that the tests can run it.
import { ChildProcess, spawn } from 'child_process';
import { Progress, parseProgressLine } from './protocol';

export interface RunRequest {
  binary: string;
  /** See `parallelArgs` */
  args: string[];
  cwd?: string;
}

export interface RunListener {
  onProgress?(progress: Progress): void;
  /** A line of stderr that is not progress, such as a panic message */
  onOutput?(line: string): void;
}

export type RunOutcome =
  | { kind: 'finished'; result: unknown }
  | { kind: 'stopped' }
  | { kind: 'failed'; message: string };

/** How long `stop` waits for the binary to exit, before it kills the binary */
const STOP_TIMEOUT_MS = 2000;
/** How many of the last lines of stderr a failure shows */
const STDERR_TAIL_LINES = 20;

/** The arguments of a binary: none for the sequential checker, and otherwise
 * `numSubTasks thresholdToParallel numSubSteps`. `workers` is 0 for all cores. */
export function parallelArgs(workers: number, thresholdToParallel: number, numSubSteps: number,
    cores: number): string[] {
  const numSubTasks = workers === 0 ? cores : workers;
  return numSubTasks <= 1 ? [] : [`${numSubTasks}`, `${thresholdToParallel}`, `${numSubSteps}`];
}

/** A running model checker binary. The binary prints progress on stderr and its result on stdout,
 * and exits as soon as its stdin is closed, so the run keeps stdin open until `stop`. */
export class CheckerRun {
  readonly outcome: Promise<RunOutcome>;
  private readonly child: ChildProcess;
  private exited = false;
  private stopRequested = false;
  private killTimer: NodeJS.Timeout | undefined;

  constructor(request: RunRequest, listener: RunListener = {}) {
    let resolve!: (outcome: RunOutcome) => void;
    let settled = false;
    this.outcome = new Promise(r => { resolve = r; });
    const settle = (outcome: RunOutcome) => {
      if (settled) return;
      settled = true;
      resolve(outcome);
    };

    const stdout: Buffer[] = [];
    const stderrTail: string[] = [];
    let partialLine = '';
    const onStderrLine = (line: string) => {
      const progress = parseProgressLine(line);
      if (progress) {
        listener.onProgress?.(progress);
      } else if (line.length > 0) {
        stderrTail.push(line);
        if (stderrTail.length > STDERR_TAIL_LINES) stderrTail.shift();
        listener.onOutput?.(line);
      }
    };

    this.child = spawn(request.binary, request.args, { cwd: request.cwd, stdio: ['pipe', 'pipe', 'pipe'] });
    // Closing the stdin of a binary that has already exited raises EPIPE
    this.child.stdin?.on('error', () => {});
    this.child.stdout?.on('data', (chunk: Buffer) => stdout.push(chunk));
    this.child.stderr?.setEncoding('utf8');
    this.child.stderr?.on('data', (chunk: string) => {
      const lines = (partialLine + chunk).split('\n');
      partialLine = lines.pop() ?? '';
      for (const line of lines) onStderrLine(line.replace(/\r$/, ''));
    });
    this.child.on('error', err => {
      this.exited = true;
      settle({ kind: 'failed', message: `Could not run ${request.binary}: ${err.message}` });
    });
    this.child.on('close', (code, signal) => {
      this.exited = true;
      if (this.killTimer) clearTimeout(this.killTimer);
      if (partialLine) onStderrLine(partialLine);
      const output = Buffer.concat(stdout).toString('utf8').trim();
      // A result counts even if it was printed just before a stop
      if (code === 0 && output) {
        try {
          settle({ kind: 'finished', result: JSON.parse(output) });
        } catch {
          settle({ kind: 'failed', message: `The model checker printed a result that is not JSON:\n${output.slice(0, 2000)}` });
        }
      } else if (this.stopRequested) {
        settle({ kind: 'stopped' });
      } else {
        const how = signal ? `was killed by ${signal}` : `exited with code ${code}`;
        const tail = stderrTail.length > 0 ? `\n${stderrTail.join('\n')}` : '';
        settle({ kind: 'failed', message: `The model checker ${how}.${tail}` });
      }
    });
  }

  get running(): boolean {
    return !this.exited;
  }

  /** Close the binary's stdin, which makes it exit, and kill it if it has not exited soon after. */
  stop(): void {
    if (this.exited || this.stopRequested) return;
    this.stopRequested = true;
    this.child.stdin?.end();
    this.killTimer = setTimeout(() => {
      if (!this.exited) this.child.kill('SIGKILL');
    }, STOP_TIMEOUT_MS);
  }
}
