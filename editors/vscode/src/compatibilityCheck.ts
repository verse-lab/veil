// Telling the user when this extension does not support the Veil of a project: once per project
// from the lenses, and whenever a command would act on such a project.
import * as vscode from 'vscode';
import { Compatibility, Incompatibility, compatibility, incompatibilityMessage, isIncompatible } from './compatibility';
import { veilProtocol } from './leanQueries';

/** How long a command waits for Lean to tell the IDE protocol, before it goes on without */
const COMMAND_TIMEOUT_MS = 2000;

export class VeilCompatibility implements vscode.Disposable {
  /** The keys (see `key`) that the user chose to use anyway, in this window */
  private readonly ignored = new Set<string>();
  /** The keys that the lenses have told the user about */
  private readonly warned = new Set<string>();
  /** The pending requests for the IDE protocol of each version of a document */
  private readonly pending = new Map<string, Promise<number | undefined>>();
  private readonly changed = new vscode.EventEmitter<void>();
  /** Fires when the user chooses to use a Veil anyway, so that the lenses show their actions again */
  readonly onDidChange = this.changed.event;

  constructor(private readonly extension: vscode.Extension<unknown>, private readonly output: vscode.OutputChannel) {}

  private get version(): string {
    return (this.extension.packageJSON as { version?: string }).version ?? '(unknown version)';
  }

  /** What "use anyway" and the warning of the lenses are per: the workspace folder of `document`, and
   * the IDE protocol of its Veil */
  private key(document: vscode.TextDocument, protocol: number): string {
    return `${vscode.workspace.getWorkspaceFolder(document.uri)?.uri.toString() ?? ''}\n${protocol}`;
  }

  /** The IDE protocol of the Veil of `document`. Lean is asked again for each check, since it loads
   * another Veil when the file restarts after the Veil of the project has changed. */
  private protocolOf(document: vscode.TextDocument): Promise<number | undefined> {
    const key = `${document.uri.toString()}#${document.version}`;
    let request = this.pending.get(key);
    if (!request) {
      request = veilProtocol(document).catch(() => undefined).finally(() => this.pending.delete(key));
      this.pending.set(key, request);
    }
    return request;
  }

  /** Whether this extension supports the Veil of `document`, as far as Lean says within `timeoutMs`.
   * A Veil that the user chose to use anyway counts as supported. */
  private async check(document: vscode.TextDocument, timeoutMs?: number): Promise<Compatibility> {
    const request = this.protocolOf(document);
    const protocol = await (timeoutMs === undefined ? request
      : Promise.race([request, new Promise<undefined>(resolve => setTimeout(resolve, timeoutMs))]));
    const found = compatibility(protocol);
    return isIncompatible(found) && this.ignored.has(this.key(document, found.protocol)) ? { kind: 'supported' } : found;
  }

  /** What to tell the user about `veil` */
  describe(veil: Incompatibility): string {
    return incompatibilityMessage(veil, this.version);
  }

  /** For the lenses of `document`: the Veil of the file, if this extension does not support it. The
   * first time for a project, this also tells the user. */
  async forLenses(document: vscode.TextDocument): Promise<Incompatibility | undefined> {
    const found = await this.check(document);
    if (!isIncompatible(found)) return undefined;
    const key = this.key(document, found.protocol);
    if (!this.warned.has(key)) {
      this.warned.add(key);
      void this.warn(document, found, false);
    }
    return found;
  }

  /** Whether a command may act on `document`: not if this extension does not support its Veil, unless
   * the user chooses to use it anyway. A Veil that Lean says nothing about in time does not stop it. */
  async beforeCommand(document: vscode.TextDocument): Promise<boolean> {
    const found = await this.check(document, COMMAND_TIMEOUT_MS);
    if (!isIncompatible(found)) return true;
    this.warned.add(this.key(document, found.protocol));
    return this.warn(document, found, true);
  }

  /** Whether Lean says nothing about the Veil of `document`, after it has processed the file */
  async isUnknown(document: vscode.TextDocument): Promise<boolean> {
    return (await this.check(document)).kind === 'unknown';
  }

  /** Tell the user why this extension does not support the Veil of `document`, for a lens */
  async explain(document: vscode.TextDocument): Promise<void> {
    const found = await this.check(document);
    if (isIncompatible(found)) await this.warn(document, found, true);
  }

  /** Tell the user about `veil`, and whether they choose to use it anyway. A command asks in a modal
   * dialog, since it waits for the answer. */
  private async warn(document: vscode.TextDocument, veil: Incompatibility, modal: boolean): Promise<boolean> {
    const message = this.describe(veil);
    this.output.appendLine(`[${new Date().toLocaleTimeString()}] ${vscode.workspace.asRelativePath(document.uri)}: ${message}`);
    const choice = await vscode.window.showWarningMessage(message, { modal }, 'Show Extension', 'Use Anyway');
    if (choice === 'Show Extension') {
      void vscode.commands.executeCommand('extension.open', this.extension.id).then(undefined, () => undefined);
    }
    if (choice !== 'Use Anyway') return false;
    this.ignored.add(this.key(document, veil.protocol));
    this.changed.fire();
    return true;
  }

  dispose(): void {
    this.changed.dispose();
  }
}
