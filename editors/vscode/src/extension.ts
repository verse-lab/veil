import * as fs from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import { findBuildCommands } from './buildCommands';
import { BuildCommand, BuildCommandLenses, buildCommandsOf, outcomeIcons } from './codeLens';
import { ModelCheckPanel, PanelContent } from './panel';
import { FORMAT_VERSION, Freshness, ResultStore, RunSource, SavedRun, freshness, parseRunFile } from './resultStore';
import { RunManager, RunTarget, sourceOf } from './runManager';
import { describeRun } from './snapshot';

function firstLine(text: string): string {
  return text.split('\n', 1)[0];
}

/** E.g. `20261018-140203`, for the names of files */
function timestamp(epochMs: number): string {
  const d = new Date(epochMs);
  const pad = (n: number) => String(n).padStart(2, '0');
  return `${d.getFullYear()}${pad(d.getMonth() + 1)}${pad(d.getDate())}-${pad(d.getHours())}${pad(d.getMinutes())}${pad(d.getSeconds())}`;
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

/** Open the file of `source` at its command, wherever the command is now in the file */
async function revealSource(source: RunSource): Promise<vscode.TextDocument | undefined> {
  let document: vscode.TextDocument;
  try {
    document = await vscode.workspace.openTextDocument(vscode.Uri.parse(source.file));
  } catch {
    void vscode.window.showWarningMessage('The file of this model check is gone.');
    return undefined;
  }
  const site = findBuildCommands(document.getText()).find(s => s.command === source.command);
  const position = new vscode.Position(site?.line ?? 0, 0);
  await vscode.window.showTextDocument(document,
    { selection: new vscode.Range(position, position), viewColumn: vscode.ViewColumn.One, preview: false });
  return document;
}

export function activate(context: vscode.ExtensionContext): void {
  const output = vscode.window.createOutputChannel('Veil Model Checker');
  // Without a workspace, e.g. for a single file, the results are kept for all windows
  const store = new ResultStore(vscode.Uri.joinPath(context.storageUri ?? context.globalStorageUri, 'results').fsPath);
  const runs = new RunManager(output, store);
  const statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left);
  statusBar.command = 'veil.modelCheck.showPanel';

  const start = (target: RunTarget): void => {
    if (runs.isRunning) {
      void vscode.window.showWarningMessage('Another model check is running.', 'Show')
        .then(choice => choice && panel.showLive(false));
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
    panel.showLive(true);
  };

  const runCommand = (document: vscode.TextDocument, { site, status }: BuildCommand): void => {
    switch (status.kind) {
      case 'pending':
        void vscode.window.showInformationMessage('Lean has not finished building this model checker yet.');
        return;
      case 'failed':
        void vscode.window.showErrorMessage(`The model checker could not be built: ${firstLine(status.message)}`,
          'Show Problems').then(choice => choice && vscode.commands.executeCommand('workbench.actions.view.problems'));
        return;
      case 'built':
        start({ uri: document.uri, line: site.line, module: site.module, command: site.command, binary: status.binary });
    }
  };

  const run = async (uri?: string, line?: number): Promise<void> => {
    const command = await pickCommand(uri, line);
    if (command) runCommand(command.document, command);
  };

  /** Run the command of a saved run, if it is still in its file */
  const runSource = async (source: RunSource): Promise<void> => {
    const document = await revealSource(source);
    if (!document) return;
    const command = buildCommandsOf(document).find(c => c.site.command === source.command);
    if (command) runCommand(document, command);
    else void vscode.window.showWarningMessage('This `#model_check_build` command is no longer in its file.');
  };

  const runAgain = (): void => {
    // After a reload, the last run is the one saved last
    const newest = store.newest();
    if (runs.lastTarget) start(runs.lastTarget);
    else if (newest) void runSource(newest.source);
  };

  /** The run that `shown` shows, as it is exported, once it has ended */
  const savedRunOf = (shown: PanelContent): SavedRun | undefined => {
    if (shown.origin !== 'live') return shown.saved;
    if (!runs.snapshot || !runs.lastTarget || runs.isRunning) return undefined;
    return { formatVersion: FORMAT_VERSION, source: sourceOf(runs.lastTarget), run: runs.snapshot };
  };

  const exportRun = async (shown: PanelContent = panel.shown): Promise<void> => {
    const saved = savedRunOf(shown);
    if (!saved) {
      void vscode.window.showInformationMessage('There is no finished model check to export.');
      return;
    }
    const folder = vscode.workspace.workspaceFolders?.[0]?.uri;
    const name = `${saved.run.module}-${timestamp(saved.run.endedAt ?? Date.now())}.json`;
    const uri = await vscode.window.showSaveDialog({
      defaultUri: folder && vscode.Uri.joinPath(folder, name),
      filters: { 'Model checking results': ['json'] },
      saveLabel: 'Export',
    });
    if (!uri) return;
    await vscode.workspace.fs.writeFile(uri, Buffer.from(JSON.stringify(saved, null, 2)));
    void vscode.window.showInformationMessage(`Exported the result to ${vscode.workspace.asRelativePath(uri)}.`);
  };

  const openRun = async (): Promise<void> => {
    const [uri] = await vscode.window.showOpenDialog({
      canSelectMany: false,
      filters: { 'Model checking results': ['json'] },
      openLabel: 'Open',
    }) ?? [];
    if (!uri) return;
    const [bytes, stat] = await Promise.all([vscode.workspace.fs.readFile(uri), vscode.workspace.fs.stat(uri)]);
    const saved = parseRunFile(Buffer.from(bytes).toString('utf8'), uri.fsPath, stat.mtime);
    if (saved) panel.showSaved(saved, 'file', path.basename(uri.fsPath));
    else void vscode.window.showErrorMessage(`${path.basename(uri.fsPath)} has no model checking result.`);
  };

  const showSavedRun = async (source: RunSource): Promise<void> => {
    const saved = await store.read(source);
    if (saved) panel.showSaved(saved, 'saved');
    else void vscode.window.showWarningMessage('This result is no longer saved.');
  };

  /** Whether `saved` is of the binary that Lean builds for its command now, as far as the open files
   * tell: Lean builds the commands of open files only */
  const freshnessOf = (saved: SavedRun): Freshness => {
    const source = saved.source;
    const document = source && vscode.workspace.textDocuments.find(d => d.uri.toString() === source.file);
    const command = document && buildCommandsOf(document).find(c => c.site.command === source.command);
    return command ? freshness(saved.run.binary, command.status) : 'unknown';
  };

  const panel = new ModelCheckPanel(context.extensionUri, runs, {
    stop: () => runs.stop(),
    runAgain: shown => {
      if (shown.origin === 'live') runAgain();
      else if (shown.saved.source) void runSource(shown.saved.source);
    },
    export: shown => void exportRun(shown),
    showOutput: () => output.show(true),
    openSource: shown => {
      const source = shown.origin === 'live' ? runs.lastTarget && sourceOf(runs.lastTarget) : shown.saved.source;
      if (source) void revealSource(source);
    },
  }, freshnessOf);
  const lenses = new BuildCommandLenses(runs, store);

  const updateStatus = (): void => {
    void vscode.commands.executeCommand('setContext', 'veil.modelCheck.isRunning', runs.isRunning);
    void vscode.commands.executeCommand('setContext', 'veil.modelCheck.canRunAgain',
      runs.lastTarget !== undefined || store.newest() !== undefined);
    const snapshot = runs.snapshot;
    if (!snapshot) {
      statusBar.hide();
      return;
    }
    const { kind, text } = describeRun(snapshot);
    statusBar.text = `${outcomeIcons[kind]} Veil: ${snapshot.module}`;
    statusBar.tooltip = `${text} (${snapshot.source}). Click to show it.`;
    statusBar.show();
  };

  context.subscriptions.push(
    output, runs, panel, lenses, statusBar,
    vscode.languages.registerCodeLensProvider({ language: 'lean4' }, lenses),
    vscode.commands.registerCommand('veil.modelCheck.run', run),
    vscode.commands.registerCommand('veil.modelCheck.runAgain', runAgain),
    vscode.commands.registerCommand('veil.modelCheck.stop', () => runs.stop()),
    // The status bar shows the run of this window
    vscode.commands.registerCommand('veil.modelCheck.showPanel',
      () => runs.snapshot ? panel.showLive(false) : panel.show(false)),
    vscode.commands.registerCommand('veil.modelCheck.showSavedRun', showSavedRun),
    vscode.commands.registerCommand('veil.modelCheck.exportResult', () => exportRun()),
    vscode.commands.registerCommand('veil.modelCheck.openResult', openRun),
    runs.onDidChangeStatus(updateStatus),
  );
  void store.load().then(() => {
    lenses.refresh();
    updateStatus();
  });
}

export function deactivate(): void {}
