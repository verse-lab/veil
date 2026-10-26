import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as vscode from 'vscode';
import { findBuildCommands } from './buildCommands';
import { checkModel, createConfig } from './checkModel';
import { BuildCommand, BuildCommandLenses, buildCommandsOf, outcomeIcons } from './codeLens';
import { ConfigTemplate } from './configTemplate';
import { askLean } from './leanQueries';
import { ModelCheckPanel, PanelContent } from './panel';
import { FORMAT_VERSION, Freshness, ResultStore, RunSource, SavedRun, freshness, parseRunFile } from './resultStore';
import { RunManager, RunTarget, sourceOf } from './runManager';
import { parallelArgs, parseRunOptions } from './runner';
import { DeclSource, ModuleSources, describeRun } from './snapshot';

/** The kind of the code action that gives where the declarations of a module are, as `moduleSourcesKind` in Lean */
const MODULE_SOURCES_KIND = 'refactor.veil.modelCheckSources';
/** How long a run waits for Lean to say where the declarations of its module are, before it starts
 * without */
const SOURCES_TIMEOUT_MS = 2000;

/** Where the declarations of the module of `target` are, as Lean says for its command */
async function requestSources(target: RunTarget): Promise<ModuleSources | undefined> {
  const asked = vscode.workspace.openTextDocument(target.uri)
    .then(document => askLean(document, target.line, MODULE_SOURCES_KIND, 'veil.modelCheck.sources'))
    .then(args => args?.[0] as ModuleSources | undefined, () => undefined);
  return Promise.race([asked, new Promise<undefined>(resolve => setTimeout(resolve, SOURCES_TIMEOUT_MS))]);
}

function firstLine(text: string): string {
  return text.split('\n', 1)[0];
}

/** E.g. `20261018-140203`, for the names of files */
function timestamp(epochMs: number): string {
  const d = new Date(epochMs);
  const pad = (n: number) => String(n).padStart(2, '0');
  return `${d.getFullYear()}${pad(d.getMonth() + 1)}${pad(d.getDate())}-${pad(d.getHours())}${pad(d.getMinutes())}${pad(d.getSeconds())}`;
}

/** The `#mc_config` command to run: the one that a lens gives, else the one at the cursor,
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
      void vscode.window.showInformationMessage('Open a Lean file with a `#mc_config` command.');
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
    void vscode.window.showInformationMessage('This file has no `#mc_config` command.');
    return undefined;
  }
  const item = await vscode.window.showQuickPick(
    commands.map(c => ({ label: c.site.module, description: `line ${c.site.line + 1}`, command: c })),
    { placeHolder: 'Select the model checker to run' });
  return item && { document, ...item.command };
}

/** The arguments of a binary for one run, which the user picks: all cores, sequential, or their own.
 * The other runs follow the settings. */
async function pickRunOptions(): Promise<string[] | undefined> {
  const config = vscode.workspace.getConfiguration('veil.modelChecker');
  const cores = os.cpus().length;
  const defaults = { thresholdToParallel: config.get('thresholdToParallel', 20), numSubSteps: config.get('numSubSteps', 1) };
  const item = await vscode.window.showQuickPick([
    { label: '$(server-process) All cores', description: `${cores} workers`,
      args: parallelArgs(0, defaults.thresholdToParallel, defaults.numSubSteps, cores) },
    { label: '$(arrow-right) Sequential', description: 'the sequential model checker', args: [] },
    { label: '$(edit) Custom...', description: 'workers, threshold to parallelize, steps', args: undefined },
  ], { placeHolder: 'How to run this model check: the settings set how the other runs go' });
  if (!item || item.args) return item?.args;
  const text = await vscode.window.showInputBox({
    prompt: 'Workers (0 for all cores, 1 for the sequential model checker), then optionally the frontier size ' +
      'from which to explore in parallel, and the steps of a worker before the frontier is merged',
    value: `${config.get('workers', 0)} ${defaults.thresholdToParallel} ${defaults.numSubSteps}`,
    validateInput: text => {
      const args = parseRunOptions(text, defaults, cores);
      return Array.isArray(args) ? undefined : args.error;
    },
  });
  const args = text === undefined ? undefined : parseRunOptions(text, defaults, cores);
  return Array.isArray(args) ? args : undefined;
}

/** Open the file of an action or a property of a module at it */
async function openLocation(location: DeclSource): Promise<void> {
  const position = new vscode.Position(location.line, location.character);
  try {
    await vscode.window.showTextDocument(vscode.Uri.file(path.normalize(location.file)),
      { selection: new vscode.Range(position, position), viewColumn: vscode.ViewColumn.One, preview: false });
  } catch {
    void vscode.window.showWarningMessage(`${location.file} cannot be opened.`);
  }
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
  const output = vscode.window.createOutputChannel('Veil');
  // Without a workspace, e.g. for a single file, the results are kept for all windows
  const store = new ResultStore(
    vscode.Uri.joinPath(context.storageUri ?? context.globalStorageUri, 'results').fsPath,
    () => vscode.workspace.getConfiguration('veil.modelChecker').get('maxSavedResults', 50));
  const runs = new RunManager(output, store);
  const statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left);
  statusBar.command = 'veil.modelCheck.showPanel';

  const start = async (target: RunTarget): Promise<void> => {
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
    const sources = await requestSources(target);
    // Another run may have started meanwhile
    if (runs.isRunning) return;
    runs.start({ ...target, sources });
    panel.showLive(true);
  };

  /** `args` are those of the binary, if the user chose them for this run */
  const runCommand = (document: vscode.TextDocument, { site, status }: BuildCommand, args?: string[]): void => {
    switch (status.kind) {
      case 'pending':
        void vscode.window.showInformationMessage('Lean has not finished building this model checker yet.');
        return;
      case 'failed':
        void vscode.window.showErrorMessage(`The model checker could not be built: ${firstLine(status.message)}`,
          'Show Problems').then(choice => choice && vscode.commands.executeCommand('workbench.actions.view.problems'));
        return;
      case 'built':
        void start({ uri: document.uri, line: site.line, module: site.module, command: site.command, binary: status.binary, args });
    }
  };

  const run = async (uri?: string, line?: number): Promise<void> => {
    const command = await pickCommand(uri, line);
    if (command) runCommand(command.document, command);
  };

  const runWithOptions = async (uri?: string, line?: number): Promise<void> => {
    const command = await pickCommand(uri, line);
    const args = command && await pickRunOptions();
    if (command && args) runCommand(command.document, command, args);
  };

  /** Run the command of a saved run with its original arguments, if it is still in its file */
  const runSource = async (source: RunSource, args: string[]): Promise<void> => {
    const document = await revealSource(source);
    if (!document) return;
    const command = buildCommandsOf(document).find(c => c.site.command === source.command);
    if (command) runCommand(document, command, args);
    else void vscode.window.showWarningMessage('This `#mc_config` command is no longer in its file.');
  };

  const runAgain = async (): Promise<void> => {
    // After a reload, the last run is the one saved last
    const newest = store.newest();
    if (runs.lastTarget) void start(runs.lastTarget);
    else if (newest) {
      const saved = await store.read(newest.source);
      if (saved) await runSource(newest.source, saved.run.args);
      else void vscode.window.showWarningMessage('This result is no longer saved.');
    }
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
      if (shown.origin === 'live') void runAgain();
      else if (shown.saved.source) void runSource(shown.saved.source, shown.saved.run.args);
    },
    export: shown => void exportRun(shown),
    showOutput: () => output.show(true),
    openSource: shown => {
      const source = shown.origin === 'live' ? runs.lastTarget && sourceOf(runs.lastTarget) : shown.saved.source;
      if (source) void revealSource(source);
    },
    openLocation: location => void openLocation(location),
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
    vscode.commands.registerCommand('veil.modelCheck.runWithOptions', runWithOptions),
    vscode.commands.registerCommand('veil.modelCheck.checkModel',
      (uri?: string, line?: number) => checkModel((document, command) => runCommand(document, command), uri, line)),
    // The command of the code action of Lean that gives the template
    vscode.commands.registerCommand('veil.modelCheck.createConfig',
      (template: ConfigTemplate, uri: string) => createConfig(template, vscode.Uri.parse(uri))),
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
