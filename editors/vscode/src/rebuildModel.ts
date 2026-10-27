import * as fs from 'fs';
import * as vscode from 'vscode';
import { BuildAfterRestart } from './buildCommands';
import { BuildCommand, buildCommandsOf } from './codeLens';
import { ImportChanges } from './importChanges';

/** A Lean file on disk, which Lean reads when another file imports it */
function isLeanFile(document: vscode.TextDocument): boolean {
  return document.languageId === 'lean4' && document.uri.scheme === 'file';
}

function modifiedAt(uri: vscode.Uri): number | undefined {
  try {
    return fs.statSync(uri.fsPath).mtimeMs;
  } catch {
    return undefined;
  }
}

/** Keep `changes` up to date with the Lean files that VS Code opens, closes and saves, and with those
 * that change on disk */
export function watchImportChanges(changes: ImportChanges): vscode.Disposable {
  // VS Code reports the change on disk of a save later. It is skipped while the file is as saved, so
  // that a restart in between does not look out of date.
  const savedAt = new Map<string, number | undefined>();
  const changedOnDisk = (uri: vscode.Uri) => {
    if (savedAt.get(uri.toString()) !== modifiedAt(uri)) changes.changed(uri.toString());
  };
  for (const document of vscode.workspace.textDocuments) {
    if (isLeanFile(document)) changes.read(document.uri.toString(), changes.now(), document.version);
  }
  const files = vscode.workspace.createFileSystemWatcher('**/*.lean');
  return vscode.Disposable.from(
    files,
    files.onDidCreate(changedOnDisk),
    files.onDidChange(changedOnDisk),
    files.onDidDelete(uri => changes.changed(uri.toString())),
    vscode.workspace.onDidSaveTextDocument(document => {
      if (!isLeanFile(document)) return;
      savedAt.set(document.uri.toString(), modifiedAt(document.uri));
      changes.changed(document.uri.toString());
    }),
    vscode.workspace.onDidOpenTextDocument(document => {
      if (isLeanFile(document)) changes.read(document.uri.toString(), changes.now(), document.version);
    }),
    vscode.workspace.onDidCloseTextDocument(document => changes.closed(document.uri.toString())),
  );
}

/** What waiting after a restart needs: where to record that Lean reads the imports again, and the
 * versions of the Lean files saved for the run */
interface Restart {
  changes: ImportChanges;
  saved: Map<string, number>;
}

interface PreparedCommand extends BuildCommand {
  /** The config version checked before waiting for its build */
  documentVersion: number;
}

/** The command of `document` whose text is `command`, once Lean reports its result, unless the user
 * stops waiting. With `restart`, the file is restarted first, so that Lean reads its imports again. */
function untilBuilt(document: vscode.TextDocument, command: string, token: vscode.CancellationToken,
    restart?: Restart): Promise<PreparedCommand | undefined> {
  return new Promise(resolve => {
    const file = document.uri.toString();
    const version = document.version;
    const rebuilt = restart && new BuildAfterRestart();
    const restartedAt = restart?.changes.now();
    const subscriptions: vscode.Disposable[] = [];
    let waiting = true;
    const done = (built?: PreparedCommand) => {
      if (!waiting) return;
      waiting = false;
      for (const subscription of subscriptions) subscription.dispose();
      resolve(built);
    };
    const check = () => {
      const found = buildCommandsOf(document).find(c => c.site.command === command);
      if (!found) {
        void vscode.window.showWarningMessage('This `#mc_config` command changed while Lean was building it. Run it again.');
        done();
        return;
      }
      // Lean drops the old result once the restart has happened, and then reads the imports
      if (restart && found.status.kind === 'pending') restart.changes.read(file, restartedAt, version);
      const status = rebuilt ? rebuilt.observe(found.status) : found.status;
      if (status.kind !== 'pending') done({ ...found, status, documentVersion: version });
    };
    subscriptions.push(
      vscode.languages.onDidChangeDiagnostics(event => {
        if (event.uris.some(uri => uri.toString() === file)) check();
      }),
      vscode.workspace.onDidCloseTextDocument(closed => {
        if (closed.uri.toString() === file) done();
      }),
      vscode.workspace.onDidChangeTextDocument(event => {
        if (event.document === document && document.version !== version) {
          void vscode.window.showWarningMessage('The config changed while Lean was building it. Run it again.');
          done();
        }
      }),
      token.onCancellationRequested(() => done()));
    if (!restart) {
      check();
      return;
    }
    subscriptions.push(vscode.workspace.onDidSaveTextDocument(saved => {
      const other = saved.uri.toString();
      // Not a save for this run, which VS Code may report late
      if (!isLeanFile(saved) || other === file || restart.saved.get(other) === saved.version) return;
      // Lean may read the imports before or after this save, and cannot report it before it has read them
      void vscode.window.showWarningMessage('Lean files were saved while Lean rebuilt the model checker. Run it again.');
      done();
    }));
    // Subscribed first: Restart File returns before Lean reports anything
    void vscode.commands.executeCommand('lean4.restartFile').then(undefined, error => {
      void vscode.window.showErrorMessage(`Could not restart the config in Lean: ${String(error)}`);
      done();
    });
  });
}

/** The command of `document` whose text is `command`, once Lean has built its model checker from the
 * Lean files as they are, or has failed to, unless the user stops waiting. Lean files with unsaved
 * changes are saved first. Lean keeps the imports of a file from when it opened or last restarted the
 * file, so the config is restarted when they may have changed since. */
export async function rebuildModel(document: vscode.TextDocument, command: string, changes: ImportChanges):
    Promise<PreparedCommand | undefined> {
  const saved = new Map<string, number>();
  for (const other of vscode.workspace.textDocuments.filter(d => isLeanFile(d) && d.isDirty)) {
    if (!await other.save()) {
      void vscode.window.showErrorMessage('The Lean changes could not be saved. The model check was not started.');
      return undefined;
    }
    saved.set(other.uri.toString(), other.version);
    // VS Code may report the save later
    changes.changed(other.uri.toString());
  }
  const version = document.version;
  const current = buildCommandsOf(document).find(c => c.site.command === command);
  if (!current) {
    void vscode.window.showWarningMessage('This `#mc_config` command is no longer in its file.');
    return undefined;
  }
  const { status } = current;
  // Saving a config edit (e.g. limit := 3 -> 2) can leave its old success diagnostic visible
  // until Lean publishes new diagnostics. ImportChanges ignores the file itself when checking
  // imports, so that old success used to start the previous binary. Refresh once after a document
  // version change; unchanged runs still reuse the binary without restarting the file.
  const restart = current.importsOutOfDate || changes.mayHaveChanged(document.uri.toString())
    || changes.hasBeenEdited(document.uri.toString(), version)
    || status.kind === 'failed'
    // Lean keeps only the newest binaries
    || (status.kind === 'built' && !fs.existsSync(status.binary));
  if (!restart && status.kind === 'built') return { ...current, documentVersion: version };
  return vscode.window.withProgress({
    location: vscode.ProgressLocation.Notification,
    title: 'Waiting for Lean to build the model checker',
    cancellable: true,
  }, async (_, token) => {
    if (!restart) {
      const built = await untilBuilt(document, command, token);
      // When Lean opens a file with imports to rebuild, it reports them as an error
      if (built?.status.kind !== 'failed' || !built.importsOutOfDate) return built;
    }
    // Restart File acts on the last active Lean editor, not on a URI argument
    const shown = vscode.window.visibleTextEditors.find(editor => editor.document === document);
    await vscode.window.showTextDocument(document, { viewColumn: shown?.viewColumn, preview: false });
    if (token.isCancellationRequested) return undefined;
    if (document.version !== version) {
      void vscode.window.showWarningMessage('The config changed while preparing the model check. Run it again.');
      return undefined;
    }
    return untilBuilt(document, command, token, { changes, saved });
  });
}
