import * as vscode from 'vscode';
import {
  BuildCommandSite, BuildStatus, ReportedMessage, Severity, buildStatus, findBuildCommands, findVeilModules,
  headerEndLine, importsOutOfDate,
} from './buildCommands';
import { ResultStore, freshness } from './resultStore';
import { RunManager } from './runManager';
import { RunOutcomeKind } from './snapshot';
import { ModelConfigs } from './modelConfigs';

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
  /** Whether Lean reports that the imports of the file, e.g. the model, have changed since it read
   * them, so that it builds from the old ones until the file is restarted */
  importsOutOfDate: boolean;
}

export function buildCommandsOf(document: vscode.TextDocument): BuildCommand[] {
  const text = document.getText();
  const sites = findBuildCommands(text);
  if (sites.length === 0) return [];
  const messages = reportedMessages(document.uri);
  const headerEnd = headerEndLine(text);
  const outOfDate = importsOutOfDate(messages);
  return sites.map(site => ({ site, status: buildStatus(site, messages, headerEnd), importsOutOfDate: outOfDate }));
}

/** E.g. `14:02`, or `Oct 18, 14:02` for another day */
function when(epochMs: number): string {
  const date = new Date(epochMs);
  const time = date.toLocaleTimeString(undefined, { hour: '2-digit', minute: '2-digit' });
  return date.toDateString() === new Date().toDateString()
    ? time
    : `${date.toLocaleDateString(undefined, { month: 'short', day: 'numeric' })}, ${time}`;
}

/** The lenses above each `veil module` and its `#gen_executable`, to check it, and above each
 * `#mc_config` command: what Lean is doing with it, how to run it, and its last result. */
export class BuildCommandLenses implements vscode.CodeLensProvider, vscode.Disposable {
  private readonly changed = new vscode.EventEmitter<void>();
  readonly onDidChangeCodeLenses = this.changed.event;
  private readonly subscriptions: vscode.Disposable[];

  constructor(private readonly runs: RunManager, private readonly store: ResultStore,
      private readonly configs: ModelConfigs) {
    this.subscriptions = [
      vscode.languages.onDidChangeDiagnostics(event => {
        if (event.uris.some(uri => uri.path.endsWith('.lean'))) this.changed.fire();
      }),
      runs.onDidChangeStatus(() => this.changed.fire()),
      configs.onDidChange(() => this.changed.fire()),
    ];
  }

  /** Update the lenses, e.g. once the saved runs are loaded */
  refresh(): void {
    this.changed.fire();
  }

  async provideCodeLenses(document: vscode.TextDocument): Promise<vscode.CodeLens[]> {
    const modules = (await Promise.all(findVeilModules(document.getText()).map(async site => {
      const configs = site.genExecutableLine === undefined ? [] : await this.configs.ofModule(site.name);
      const [title, tooltip] = site.genExecutableLine === undefined
        ? ['$(add) Add #gen_executable', `Add #gen_executable to ${site.name} so a config can build its model checker`]
        : configs.length === 0
          ? ['$(new-file) Create model checking config', `Create and open a config for ${site.name}, with values to fill in`]
          : configs.length === 1
            ? ['$(play) Run model checker', `Save Lean changes, rebuild what they affect, and run the model checker of the config for ${site.name}`]
            : ['$(play) Select config and run...', `Select a config for ${site.name}, save Lean changes, rebuild what they affect, and run its model checker`];
      const lines = [site.line];
      if (site.genExecutableLine !== undefined) lines.push(site.genExecutableLine);
      return lines.map(line => {
        const character = line === site.line ? site.character : 0;
        return new vscode.CodeLens(new vscode.Range(line, character, line, character), {
          title, command: 'veil.modelCheck.checkModel',
          arguments: [document.uri.toString(), site.line], tooltip,
        });
      });
    }))).flat();
    return [...modules, ...buildCommandsOf(document).flatMap(({ site, status, importsOutOfDate: outOfDate }) => {
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
      const at = [document.uri.toString(), site.line];
      const tooltip = 'Save Lean changes, rebuild what they affect, and run the model checker';
      // A run restarts the file if Lean has to read its imports again, and else waits for the build
      const run = outOfDate || status.kind === 'failed'
        ? lens('$(play) Rebuild and run model checker', 'veil.modelCheck.run', at, tooltip)
        : status.kind === 'pending'
          ? lens('$(sync~spin) Run once built', 'veil.modelCheck.run', at,
            'Lean is building the model checker. Run it once it is built.')
          : lens('$(play) Run model checker', 'veil.modelCheck.run', at, tooltip);
      const lenses = [run, lens('$(settings-gear) Run with options...', 'veil.modelCheck.runWithOptions', at)];
      // Out-of-date imports are what a rebuild fixes, rather than an error to show
      if (status.kind === 'failed' && !outOfDate) {
        lenses.push(lens('$(error) The model checker could not be built', 'workbench.actions.view.problems'));
      }
      const saved = this.store.summary({ file: document.uri.toString(), command: site.command });
      if (saved && freshness(saved.binary, status, outOfDate) === 'outdated') {
        lenses.push(lens(`$(history) Last result (outdated) · ${when(saved.endedAt)}`, 'veil.modelCheck.showSavedRun',
          [saved.source], `${saved.text}. The model or the config has changed since this run.`));
      } else if (saved) {
        lenses.push(lens(`${outcomeIcons[saved.outcome]} Last result · ${when(saved.endedAt)}`,
          'veil.modelCheck.showSavedRun', [saved.source], saved.text));
      }
      return lenses;
    })];
  }

  dispose(): void {
    for (const subscription of this.subscriptions) subscription.dispose();
    this.changed.dispose();
  }
}
