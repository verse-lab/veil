import * as vscode from 'vscode';
import {
  BuildCommandSite, BuildStatus, ReportedMessage, Severity, buildStatus, findBuildCommands,
} from './buildCommands';
import { RunManager } from './runManager';

const severities: Record<vscode.DiagnosticSeverity, Severity> = {
  [vscode.DiagnosticSeverity.Error]: 'error',
  [vscode.DiagnosticSeverity.Warning]: 'warning',
  [vscode.DiagnosticSeverity.Information]: 'information',
  [vscode.DiagnosticSeverity.Hint]: 'hint',
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

/** The lenses above each `#model_check_build` command: what Lean is doing with it, or how to run it. */
export class BuildCommandLenses implements vscode.CodeLensProvider, vscode.Disposable {
  private readonly changed = new vscode.EventEmitter<void>();
  readonly onDidChangeCodeLenses = this.changed.event;
  private readonly subscriptions: vscode.Disposable[];

  constructor(private readonly runs: RunManager) {
    this.subscriptions = [
      vscode.languages.onDidChangeDiagnostics(event => {
        if (event.uris.some(uri => uri.path.endsWith('.lean'))) this.changed.fire();
      }),
      runs.onDidChangeStatus(() => this.changed.fire()),
    ];
  }

  provideCodeLenses(document: vscode.TextDocument): vscode.CodeLens[] {
    return buildCommandsOf(document).flatMap(({ site, status }) => {
      const range = new vscode.Range(site.line, site.character, site.line, site.character);
      // A lens without a command shows as plain text
      const lens = (title: string, command = '', args: unknown[] = []) =>
        new vscode.CodeLens(range, { title, command, arguments: args });
      switch (status.kind) {
        case 'pending':
          return [lens('$(sync~spin) Waiting for Lean to build the model checker')];
        case 'failed':
          return [lens('$(error) The model checker could not be built', 'workbench.actions.view.problems')];
        case 'built': {
          if (this.runs.isRunningBinary(status.binary)) {
            return [
              lens('$(debug-stop) Stop model checking', 'veil.modelCheck.stop'),
              lens('$(open-preview) Show progress', 'veil.modelCheck.showPanel'),
            ];
          }
          const lenses = [lens('$(play) Run model checker', 'veil.modelCheck.run', [document.uri.toString(), site.line])];
          if (this.runs.snapshot?.binary === status.binary) {
            lenses.push(lens('$(open-preview) Show last result', 'veil.modelCheck.showPanel'));
          }
          return lenses;
        }
      }
    });
  }

  dispose(): void {
    for (const subscription of this.subscriptions) subscription.dispose();
    this.changed.dispose();
  }
}
