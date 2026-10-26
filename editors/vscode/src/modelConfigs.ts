import * as vscode from 'vscode';
import { BuildCommandSite, findBuildCommands } from './buildCommands';
import { isOfModule } from './configTemplate';

interface ModelConfig {
  uri: vscode.Uri;
  site: BuildCommandSite;
}

/** The workspace's config commands, shared by the module lenses and their action. */
export class ModelConfigs implements vscode.Disposable {
  private configs: Promise<ModelConfig[]> | undefined;
  private readonly changed = new vscode.EventEmitter<void>();
  readonly onDidChange = this.changed.event;
  private readonly subscriptions: vscode.Disposable[];

  constructor() {
    const refresh = (uri: vscode.Uri) => {
      if (!uri.path.endsWith('.lean') || /\/(?:\.lake|node_modules)\//.test(uri.path)) return;
      this.configs = undefined;
      this.changed.fire();
    };
    const files = vscode.workspace.createFileSystemWatcher('**/*.lean');
    this.subscriptions = [
      files,
      files.onDidCreate(refresh),
      files.onDidChange(refresh),
      files.onDidDelete(refresh),
      vscode.workspace.onDidChangeTextDocument(event => {
        if (event.contentChanges.length > 0) refresh(event.document.uri);
      }),
      vscode.workspace.onDidCloseTextDocument(document => refresh(document.uri)),
      vscode.workspace.onDidChangeWorkspaceFolders(() => {
        this.configs = undefined;
        this.changed.fire();
      }),
    ];
  }

  /** Open files override their saved contents. */
  private async readConfigs(): Promise<ModelConfig[]> {
    const uris = await vscode.workspace.findFiles('**/*.lean', '{**/.lake/**,**/node_modules/**}');
    const configs: ModelConfig[] = [];
    for (const uri of uris) {
      const open = vscode.workspace.textDocuments.find(d => d.uri.toString() === uri.toString());
      let text: string;
      try {
        text = open ? open.getText() : Buffer.from(await vscode.workspace.fs.readFile(uri)).toString('utf8');
      } catch (error) {
        // A config may have been deleted while the workspace was being read.
        if (error instanceof vscode.FileSystemError && error.code === 'FileNotFound') continue;
        throw error;
      }
      if (!text.includes('#mc_config')) continue;
      for (const site of findBuildCommands(text)) configs.push({ uri, site });
    }
    return configs;
  }

  async ofModule(name: string): Promise<ModelConfig[]> {
    this.configs ??= this.readConfigs();
    return (await this.configs).filter(config => isOfModule(config.site.module, name));
  }

  dispose(): void {
    for (const subscription of this.subscriptions) subscription.dispose();
    this.changed.dispose();
  }
}
