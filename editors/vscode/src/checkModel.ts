// "Check Model": from a `veil module`, run the model checker of a config file of it, or else create
// a config file from the template that Lean gives.
import * as path from 'path';
import * as vscode from 'vscode';
import { VeilModuleSite, findVeilModules } from './buildCommands';
import { BuildCommand, buildCommandsOf } from './codeLens';
import { ConfigTemplate, SnippetPart, configCommand, configFileFor, configHeader, isOfModule } from './configTemplate';
import { askLeanCommands, hasExecutableDefinitions } from './leanQueries';
import { ModelConfigs } from './modelConfigs';

/** The kind of the code action that gives the template, as `configTemplateKind` in Lean */
const CONFIG_TEMPLATE_KIND = 'refactor.veil.modelCheckConfig';

/** The `veil module` to check: the one that a lens gives, else the one at the cursor, else the only
 * one in the editor, else one that the user picks */
async function pickModule(uri?: string, line?: number):
    Promise<{ document: vscode.TextDocument; site: VeilModuleSite } | undefined> {
  let document: vscode.TextDocument;
  let isWanted: (site: VeilModuleSite) => boolean;
  if (uri !== undefined && line !== undefined) {
    document = await vscode.workspace.openTextDocument(vscode.Uri.parse(uri));
    isWanted = site => site.line === line;
  } else {
    const editor = vscode.window.activeTextEditor;
    if (!editor || editor.document.languageId !== 'lean4') {
      void vscode.window.showInformationMessage('Open a Lean file with a `veil module`.');
      return undefined;
    }
    document = editor.document;
    const cursor = editor.selection.active.line;
    isWanted = site => site.line <= cursor && cursor <= (site.endLine ?? document.lineCount);
  }
  const modules = findVeilModules(document.getText());
  const site = modules.find(isWanted) ?? (modules.length === 1 ? modules[0] : undefined);
  if (site) return { document, site };
  if (modules.length === 0) {
    void vscode.window.showInformationMessage('This file has no `veil module`.');
    return undefined;
  }
  const item = await vscode.window.showQuickPick(
    modules.map(m => ({ label: m.name, description: `line ${m.line + 1}`, site: m })),
    { placeHolder: 'Select the module to check' });
  return item && { document, site: item.site };
}

/** Add `#gen_executable` to a module: after its `#gen_spec`, which it needs, or else before its `end` */
async function addGenExecutable(document: vscode.TextDocument, site: VeilModuleSite): Promise<void> {
  const edit = new vscode.WorkspaceEdit();
  if (site.genSpecLine !== undefined) {
    edit.insert(document.uri, new vscode.Position(site.genSpecLine + 1, 0), '\n#gen_executable\n');
  } else {
    edit.insert(document.uri, new vscode.Position(site.endLine ?? document.lineCount, 0), '#gen_executable\n\n');
  }
  await vscode.workspace.applyEdit(edit);
}

/** The template of a config file, after the module's executable definitions have been generated */
async function requestTemplate(document: vscode.TextDocument, line: number, module: string): Promise<ConfigTemplate | undefined> {
  const commands = await askLeanCommands(document, line, CONFIG_TEMPLATE_KIND, 'veil.modelCheck.createConfig');
  return commands.map(args => args[0] as ConfigTemplate).find(template => isOfModule(module, template.module));
}

function toSnippet(parts: SnippetPart[]): vscode.SnippetString {
  const snippet = new vscode.SnippetString();
  for (const part of parts) {
    if ('text' in part) snippet.appendText(part.text);
    else snippet.appendPlaceholder(part.placeholder);
  }
  return snippet;
}

/** Create a config file for the module of `moduleUri` from `template`, and let the user fill in its
 * values, from one placeholder to the next */
export async function createConfig(template: ConfigTemplate, moduleUri: vscode.Uri): Promise<void> {
  if (!template.import) {
    void vscode.window.showWarningMessage(`The file of module ${template.module} is in no library of the ` +
      'lakefile, so that no config file can import it.');
    return;
  }
  let file = vscode.Uri.file(configFileFor(moduleUri.fsPath));
  const exists = await vscode.workspace.fs.stat(file).then(() => true, () => false);
  if (exists) {
    const chosen = await vscode.window.showSaveDialog(
      { defaultUri: file, filters: { Lean: ['lean'] }, saveLabel: 'Create', title: 'Create a config file' });
    if (!chosen) return;
    file = chosen;
  }
  await vscode.workspace.fs.writeFile(file, Buffer.from(configHeader(template)));
  const editor = await vscode.window.showTextDocument(file, { preview: false });
  await editor.insertSnippet(toSnippet(configCommand(template)), editor.document.lineAt(editor.document.lineCount - 1).range.end);
}

/** "Check Model": run the model checker of a config file of a module, once Lean has built it, or else
 * create a config file for the module. `run` runs the command of a config file. */
export async function checkModel(run: (document: vscode.TextDocument, command: BuildCommand) => Promise<void>,
    modelConfigs: ModelConfigs, uri?: string, line?: number): Promise<void> {
  const picked = await pickModule(uri, line);
  if (!picked) return;
  const { document, site } = picked;
  if (!await hasExecutableDefinitions(document, site)) {
    // The lens already names the edit; the generic command-palette entry still needs to ask.
    if (uri === undefined || line === undefined) {
      const add = await vscode.window.showWarningMessage(`Module ${site.name} has no \`#gen_executable\`, which a ` +
        'config file needs to build its model checker.', 'Add #gen_executable');
      if (!add) return;
    }
    await addGenExecutable(document, site);
    return;
  }
  const configs = await modelConfigs.ofModule(site.name);
  if (configs.length === 0) {
    // At `#gen_executable`, Lean answers without processing the rest of the module first
    const askAt = site.genExecutableLine ?? site.endLine ?? document.lineCount - 1;
    const template = await vscode.window.withProgress(
      { location: vscode.ProgressLocation.Notification, title: `Asking Lean for a config template for ${site.name}` },
      () => requestTemplate(document, askAt, site.name));
    if (template) await createConfig(template, document.uri);
    else void vscode.window.showWarningMessage(`Lean has no config template for ${site.name}: check that Lean ` +
      'processes its `#gen_executable`, `#model_check` or `#simulate` without errors.');
    return;
  }
  const config = configs.length === 1 ? configs[0] : (await vscode.window.showQuickPick(
    configs.map(c => ({
      label: path.basename(c.uri.fsPath), description: `line ${c.site.line + 1}`, detail: c.site.command, config: c,
    })),
    { placeHolder: `Select the config of ${site.name} to run` }))?.config;
  if (!config) return;
  const configDocument = await vscode.workspace.openTextDocument(config.uri);
  const position = new vscode.Position(config.site.line, 0);
  await vscode.window.showTextDocument(configDocument,
    { selection: new vscode.Range(position, position), preview: false });
  const command = buildCommandsOf(configDocument).find(c => c.site.command === config.site.command);
  if (command) await run(configDocument, command);
}
