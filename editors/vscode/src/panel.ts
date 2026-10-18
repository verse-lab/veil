import { randomBytes } from 'crypto';
import * as vscode from 'vscode';
import { Freshness, SavedRun } from './resultStore';
import { RunManager } from './runManager';
import { ExtensionMessage, PanelMessage, PanelState } from './snapshot';

/** How often the panel is updated while a binary reports progress, as in TLC's extension */
const UPDATE_INTERVAL_MS = 500;

/** What the panel shows: the current or last run of this window, or a run that was saved before or
 * that the user opened from a file */
export type PanelContent =
  | { origin: 'live' }
  | { origin: 'saved' | 'file'; saved: SavedRun; fileName?: string };

/** What the buttons of the panel do, to what it shows */
export interface PanelActions {
  stop(): void;
  runAgain(shown: PanelContent): void;
  export(shown: PanelContent): void;
  showOutput(): void;
  openSource(shown: PanelContent): void;
}

/** The "Veil Model Checking" panel. */
export class ModelCheckPanel implements vscode.Disposable {
  private panel: vscode.WebviewPanel | undefined;
  private content: PanelContent = { origin: 'live' };
  private updateTimer: NodeJS.Timeout | undefined;
  private readonly subscriptions: vscode.Disposable[];

  /** `freshnessOf` tells whether a saved run is of the binary that Lean builds now */
  constructor(private readonly extensionUri: vscode.Uri, private readonly runs: RunManager,
      private readonly actions: PanelActions, private readonly freshnessOf: (saved: SavedRun) => Freshness) {
    this.subscriptions = [
      runs.onDidChangeStatus(() => this.update()),
      runs.onDidProgress(() => {
        if (this.content.origin === 'live') this.scheduleUpdate();
      }),
      // Lean may build another binary for the command of a saved run
      vscode.languages.onDidChangeDiagnostics(() => {
        if (this.content.origin !== 'live') this.scheduleUpdate();
      }),
    ];
  }

  get shown(): PanelContent {
    return this.content;
  }

  /** Show the panel, with what it showed before */
  show(preserveFocus: boolean): void {
    if (this.panel) {
      this.panel.reveal(undefined, preserveFocus);
      return;
    }
    const panel = vscode.window.createWebviewPanel('veil.modelCheck', 'Veil Model Checking',
      { viewColumn: vscode.ViewColumn.Beside, preserveFocus },
      { enableScripts: true, localResourceRoots: [vscode.Uri.joinPath(this.extensionUri, 'dist')] });
    panel.webview.html = this.html(panel.webview);
    panel.webview.onDidReceiveMessage((message: PanelMessage) => this.receive(message));
    panel.onDidDispose(() => {
      this.panel = undefined;
    });
    this.panel = panel;
  }

  /** Show the current or last run of this window */
  showLive(preserveFocus: boolean): void {
    this.content = { origin: 'live' };
    this.show(preserveFocus);
    this.update();
  }

  showSaved(saved: SavedRun, origin: 'saved' | 'file', fileName?: string): void {
    this.content = { origin, saved, fileName };
    this.show(false);
    this.update();
  }

  private state(): PanelState | null {
    const content = this.content;
    // One model check runs at a time
    const idle = !this.runs.isRunning;
    if (content.origin === 'live') {
      const run = this.runs.snapshot;
      return run ? { run, origin: 'live', canRunAgain: idle && this.runs.lastTarget !== undefined } : null;
    }
    return {
      run: content.saved.run, origin: content.origin, fileName: content.fileName,
      canRunAgain: idle && content.saved.source !== undefined,
      outdated: this.freshnessOf(content.saved) === 'outdated',
    };
  }

  private receive(message: PanelMessage): void {
    switch (message.type) {
      case 'ready':
        // The webview has (re)loaded, e.g. after it was hidden
        this.update();
        break;
      case 'stop':
        this.actions.stop();
        break;
      case 'runAgain':
        this.actions.runAgain(this.content);
        break;
      case 'export':
        this.actions.export(this.content);
        break;
      case 'showOutput':
        this.actions.showOutput();
        break;
      case 'openSource':
        this.actions.openSource(this.content);
        break;
    }
  }

  private scheduleUpdate(): void {
    if (this.updateTimer) return;
    this.updateTimer = setTimeout(() => this.update(), UPDATE_INTERVAL_MS);
  }

  private update(): void {
    if (this.updateTimer) clearTimeout(this.updateTimer);
    this.updateTimer = undefined;
    const message: ExtensionMessage = { type: 'state', state: this.state() };
    void this.panel?.webview.postMessage(message);
  }

  private html(webview: vscode.Webview): string {
    const script = webview.asWebviewUri(vscode.Uri.joinPath(this.extensionUri, 'dist', 'webview.js'));
    const nonce = randomBytes(16).toString('hex');
    return `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src ${webview.cspSource} 'unsafe-inline'; script-src 'nonce-${nonce}';">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Veil Model Checking</title>
</head>
<body>
<div id="root"></div>
<script nonce="${nonce}" src="${script}"></script>
</body>
</html>`;
  }

  dispose(): void {
    if (this.updateTimer) clearTimeout(this.updateTimer);
    for (const subscription of this.subscriptions) subscription.dispose();
    this.panel?.dispose();
  }
}
