// What the extension asks Lean for, with the code actions that Lean gives only to requests for their
// kinds (see `Veil/Frontend/DSL/Module/ConfigTemplate.lean`).
import * as vscode from 'vscode';

/** The arguments of `command`, the command of the code action of `kind` that Lean gives for the Lean
 * command on `line` of `document`, if Lean gives one */
export async function askLean(document: vscode.TextDocument, line: number, kind: string, command: string):
    Promise<unknown[] | undefined> {
  // Lean answers for the command that ends at the end of the range or after it: at the start of
  // the line, that would be the command before
  const actions = await vscode.commands.executeCommand<(vscode.CodeAction | vscode.Command)[]>(
    'vscode.executeCodeActionProvider', document.uri, document.lineAt(line).range, kind) ?? [];
  for (const action of actions) {
    const found = typeof action.command === 'string' ? action as vscode.Command : (action as vscode.CodeAction).command;
    if (found?.command === command) return found.arguments ?? [];
  }
  return undefined;
}
