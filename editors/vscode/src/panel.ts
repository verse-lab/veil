import { randomBytes } from 'crypto';
import * as vscode from 'vscode';
import { RunManager } from './runManager';
import { ExtensionMessage, PanelMessage } from './snapshot';

/** How often the panel is updated while a binary reports progress, as in TLC's extension */
const UPDATE_INTERVAL_MS = 500;

export interface PanelActions {
  stop(): void;
  runAgain(): void;
  showOutput(): void;
  openSource(): void;
}

/** The "Veil Model Checking" panel, which shows the current run, or else the last one. */
export class ModelCheckPanel implements vscode.Disposable {
  private panel: vscode.WebviewPanel | undefined;
  private updateTimer: NodeJS.Timeout | undefined;
  private readonly subscriptions: vscode.Disposable[];

  constructor(private readonly extensionUri: vscode.Uri, private readonly runs: RunManager,
      private readonly actions: PanelActions) {
    this.subscriptions = [
      runs.onDidChangeStatus(() => this.update()),
      runs.onDidProgress(() => this.scheduleUpdate()),
    ];
  }

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
        this.actions.runAgain();
        break;
      case 'showOutput':
        this.actions.showOutput();
        break;
      case 'openSource':
        this.actions.openSource();
        break;
      case 'copy':
        void vscode.env.clipboard.writeText(message.text);
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
    const message: ExtensionMessage = { type: 'state', state: this.runs.snapshot ?? null };
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
