// What the extension asks Lean for, with the code actions that Lean gives only to requests for their
// kinds (see `Veil/Frontend/DSL/Module/ConfigTemplate.lean`).
import * as vscode from 'vscode';
import { VeilModuleSite } from './buildCommands';
import { isOfModule } from './configTemplate';

/** The kind of the code action that gives the modules with executable definitions, as `executableModulesKind` in Lean */
const EXECUTABLE_MODULES_KIND = 'refactor.veil.executableModules';

/** The arguments of `command`, the command of the code action of `kind` that Lean gives for the Lean
 * command on `line` of `document`, if Lean gives one */
export async function askLean(document: vscode.TextDocument, line: number, kind: string, command: string):
    Promise<unknown[] | undefined> {
  return (await askLeanCommands(document, line, kind, command))[0];
}

/** All matching commands, e.g. when Lean gives templates for several modules */
export async function askLeanCommands(document: vscode.TextDocument, line: number, kind: string, command: string):
    Promise<unknown[][]> {
  // Lean answers for the command that ends at the end of the range or after it: at the start of
  // the line, that would be the command before
  const actions = await vscode.commands.executeCommand<(vscode.CodeAction | vscode.Command)[]>(
    'vscode.executeCodeActionProvider', document.uri, document.lineAt(line).range, kind) ?? [];
  const matches: unknown[][] = [];
  for (const action of actions) {
    const found = typeof action.command === 'string' ? action as vscode.Command : (action as vscode.CodeAction).command;
    if (found?.command === command) matches.push(found.arguments ?? []);
  }
  return matches;
}

/** Whether Lean has generated executable definitions, including through an execution command */
export async function hasExecutableDefinitions(document: vscode.TextDocument, site: VeilModuleSite): Promise<boolean> {
  if (site.genExecutableLine !== undefined) return true;
  const args = await askLean(document, site.endLine ?? document.lineCount - 1,
    EXECUTABLE_MODULES_KIND, 'veil.modelCheck.executableModules');
  return Array.isArray(args?.[0]) && args[0].some(name => typeof name === 'string' && isOfModule(site.name, name));
}
