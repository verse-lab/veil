import * as fs from 'fs';
import * as vscode from 'vscode';
import { BuildCommand, BuildCommandLenses, buildCommandsOf } from './codeLens';
import { ModelCheckPanel } from './panel';
import { VerdictKind, describeResult } from './protocol';
import { RunManager, RunTarget } from './runManager';
import { RunSnapshot } from './snapshot';

const verdictIcons: Record<VerdictKind, string> = {
  success: '$(pass)',
  violation: '$(error)',
  cancelled: '$(circle-slash)',
  error: '$(error)',
  unknown: '$(question)',
};

function statusIcon(snapshot: RunSnapshot): string {
  switch (snapshot.status) {
    case 'running':
    case 'stopping':
      return '$(sync~spin)';
    case 'stopped':
      return '$(circle-slash)';
    case 'failed':
      return '$(error)';
    case 'finished':
      return verdictIcons[describeResult(snapshot.result).kind];
  }
}

function firstLine(text: string): string {
  return text.split('\n', 1)[0];
}

/** The `#model_check_build` command to run: the one that a lens gives, else the one at the cursor,
 * else the only one in the editor, else one that the user picks. */
async function pickCommand(uri?: string, line?: number):
    Promise<(BuildCommand & { document: vscode.TextDocument }) | undefined> {
  let document: vscode.TextDocument;
  let isWanted: (command: BuildCommand) => boolean;
  if (uri !== undefined && line !== undefined) {
    document = await vscode.workspace.openTextDocument(vscode.Uri.parse(uri));
    isWanted = command => command.site.line === line;
  } else {
    const editor = vscode.window.activeTextEditor;
    if (!editor || editor.document.languageId !== 'lean4') {
      void vscode.window.showInformationMessage('Open a Lean file with a `#model_check_build` command.');
      return undefined;
    }
    document = editor.document;
    const cursor = editor.selection.active.line;
    isWanted = command => command.site.line <= cursor && cursor <= command.site.endLine;
  }
  const commands = buildCommandsOf(document);
  const command = commands.find(isWanted) ?? (commands.length === 1 ? commands[0] : undefined);
  if (command) return { document, ...command };
  if (commands.length === 0) {
    void vscode.window.showInformationMessage('This file has no `#model_check_build` command.');
    return undefined;
  }
  const item = await vscode.window.showQuickPick(
    commands.map(c => ({ label: c.site.module, description: `line ${c.site.line + 1}`, command: c })),
    { placeHolder: 'Select the model checker to run' });
  return item && { document, ...item.command };
}

export function activate(context: vscode.ExtensionContext): void {
  const output = vscode.window.createOutputChannel('Veil Model Checker');
  const runs = new RunManager(output);
  const statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left);
  statusBar.command = 'veil.modelCheck.showPanel';

  const openSource = (): void => {
    const target = runs.lastTarget;
    if (!target) return;
    const position = new vscode.Position(target.line, 0);
    void vscode.window.showTextDocument(target.uri,
      { selection: new vscode.Range(position, position), viewColumn: vscode.ViewColumn.One, preview: false });
  };

  const start = (target: RunTarget): void => {
    if (runs.isRunning) {
      void vscode.window.showWarningMessage('Another model check is running.', 'Show')
        .then(choice => choice && panel.show(false));
      return;
    }
    if (!fs.existsSync(target.binary)) {
      void vscode.window.showWarningMessage(
        'The binary of this model checker is gone, since Lean keeps only the newest ones. ' +
        'Restart the file in Lean to build it again.', 'Restart File')
        .then(choice => choice && vscode.commands.executeCommand('lean4.restartFile'));
      return;
    }
    runs.start(target);
    panel.show(true);
  };

  const run = async (uri?: string, line?: number): Promise<void> => {
    const command = await pickCommand(uri, line);
    if (!command) return;
    const { document, site, status } = command;
    switch (status.kind) {
      case 'pending':
        void vscode.window.showInformationMessage('Lean has not finished building this model checker yet.');
        return;
      case 'failed':
        void vscode.window.showErrorMessage(`The model checker could not be built: ${firstLine(status.message)}`,
          'Show Problems').then(choice => choice && vscode.commands.executeCommand('workbench.actions.view.problems'));
        return;
      case 'built':
        start({ uri: document.uri, line: site.line, module: site.module, binary: status.binary });
    }
  };

  const runAgain = (): void => {
    if (runs.lastTarget) start(runs.lastTarget);
  };

  const panel = new ModelCheckPanel(context.extensionUri, runs, {
    stop: () => runs.stop(),
    runAgain,
    showOutput: () => output.show(true),
    openSource,
  });
  const lenses = new BuildCommandLenses(runs);

  const updateStatus = (): void => {
    void vscode.commands.executeCommand('setContext', 'veil.modelCheck.isRunning', runs.isRunning);
    void vscode.commands.executeCommand('setContext', 'veil.modelCheck.canRunAgain', runs.lastTarget !== undefined);
    const snapshot = runs.snapshot;
    if (!snapshot) {
      statusBar.hide();
      return;
    }
    statusBar.text = `${statusIcon(snapshot)} Veil: ${snapshot.module}`;
    statusBar.tooltip = snapshot.status === 'finished'
      ? `${describeResult(snapshot.result).text} (${snapshot.source})`
      : `Model check of ${snapshot.source}: ${snapshot.status}. Click to show it.`;
    statusBar.show();
  };

  context.subscriptions.push(
    output, runs, panel, lenses, statusBar,
    vscode.languages.registerCodeLensProvider({ language: 'lean4' }, lenses),
    vscode.commands.registerCommand('veil.modelCheck.run', run),
    vscode.commands.registerCommand('veil.modelCheck.runAgain', runAgain),
    vscode.commands.registerCommand('veil.modelCheck.stop', () => runs.stop()),
    vscode.commands.registerCommand('veil.modelCheck.showPanel', () => panel.show(false)),
    runs.onDidChangeStatus(updateStatus),
  );
}

export function deactivate(): void {}
