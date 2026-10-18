import * as vscode from 'vscode';
import {
  BuildCommandSite, BuildStatus, ReportedMessage, Severity, buildStatus, findBuildCommands,
} from './buildCommands';
import { ResultStore, freshness } from './resultStore';
import { RunManager } from './runManager';
import { RunOutcomeKind } from './snapshot';

const severities: Record<vscode.DiagnosticSeverity, Severity> = {
  [vscode.DiagnosticSeverity.Error]: 'error',
  [vscode.DiagnosticSeverity.Warning]: 'warning',
  [vscode.DiagnosticSeverity.Information]: 'information',
  [vscode.DiagnosticSeverity.Hint]: 'hint',
};

/** The icons of what runs came to */
export const outcomeIcons: Record<RunOutcomeKind, string> = {
  success: '$(pass)',
  violation: '$(error)',
  cancelled: '$(circle-slash)',
  error: '$(error)',
  unknown: '$(question)',
  running: '$(sync~spin)',
  stopped: '$(circle-slash)',
  failed: '$(error)',
};

/** The messages that Lean reports for `uri`. The Lean extension publishes them as diagnostics,
 * which the public VS Code API gives us. */
export function reportedMessages(uri: vscode.Uri): ReportedMessage[] {
  return vscode.languages.getDiagnostics(uri).map(d => ({
    line: d.range.start.line,
    severity: severities[d.severity],
    message: d.message,
  }));
}

export interface BuildCommand {
  site: BuildCommandSite;
  status: BuildStatus;
}

export function buildCommandsOf(document: vscode.TextDocument): BuildCommand[] {
  const messages = reportedMessages(document.uri);
  return findBuildCommands(document.getText()).map(site => ({ site, status: buildStatus(site, messages) }));
}

/** E.g. `14:02`, or `Oct 18, 14:02` for another day */
function when(epochMs: number): string {
  const date = new Date(epochMs);
  const time = date.toLocaleTimeString(undefined, { hour: '2-digit', minute: '2-digit' });
  return date.toDateString() === new Date().toDateString()
    ? time
    : `${date.toLocaleDateString(undefined, { month: 'short', day: 'numeric' })}, ${time}`;
}

/** The lenses above each `#model_check_build` command: what Lean is doing with it, how to run it,
 * and its last result. */
export class BuildCommandLenses implements vscode.CodeLensProvider, vscode.Disposable {
  private readonly changed = new vscode.EventEmitter<void>();
  readonly onDidChangeCodeLenses = this.changed.event;
  private readonly subscriptions: vscode.Disposable[];

  constructor(private readonly runs: RunManager, private readonly store: ResultStore) {
    this.subscriptions = [
      vscode.languages.onDidChangeDiagnostics(event => {
        if (event.uris.some(uri => uri.path.endsWith('.lean'))) this.changed.fire();
      }),
      runs.onDidChangeStatus(() => this.changed.fire()),
    ];
  }

  /** Update the lenses, e.g. once the saved runs are loaded */
  refresh(): void {
    this.changed.fire();
  }

  provideCodeLenses(document: vscode.TextDocument): vscode.CodeLens[] {
    return buildCommandsOf(document).flatMap(({ site, status }) => {
      const range = new vscode.Range(site.line, site.character, site.line, site.character);
      // A lens without a command shows as plain text
      const lens = (title: string, command = '', args: unknown[] = [], tooltip?: string) =>
        new vscode.CodeLens(range, { title, command, arguments: args, tooltip });
      if (status.kind === 'built' && this.runs.isRunningBinary(status.binary)) {
        return [
          lens('$(debug-stop) Stop model checking', 'veil.modelCheck.stop'),
          lens('$(open-preview) Show progress', 'veil.modelCheck.showPanel'),
        ];
      }
      const lenses = [
        status.kind === 'built' ? lens('$(play) Run model checker', 'veil.modelCheck.run', [document.uri.toString(), site.line])
          : status.kind === 'pending' ? lens('$(sync~spin) Waiting for Lean to build the model checker')
          : lens('$(error) The model checker could not be built', 'workbench.actions.view.problems'),
      ];
      const saved = this.store.summary({ file: document.uri.toString(), command: site.command });
      if (saved && freshness(saved.binary, status) === 'outdated') {
        lenses.push(lens(`$(history) Last result (outdated) · ${when(saved.endedAt)}`, 'veil.modelCheck.showSavedRun',
          [saved.source], `${saved.text}. The model checker has changed since, e.g. because the model did.`));
      } else if (saved) {
        lenses.push(lens(`${outcomeIcons[saved.outcome]} Last result · ${when(saved.endedAt)}`,
          'veil.modelCheck.showSavedRun', [saved.source], saved.text));
      }
      return lenses;
    });
  }

  dispose(): void {
    for (const subscription of this.subscriptions) subscription.dispose();
    this.changed.dispose();
  }
}
