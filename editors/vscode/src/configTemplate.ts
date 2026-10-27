// The config files that "Check Model" creates for a module, from the template that Lean gives for it
// (see `Veil/Frontend/DSL/Module/ConfigTemplate.lean`). This module does not use VS Code, so that the
// tests can run it.
import * as path from 'path';
import { ModelCheckArguments } from './modelCheckCommands';

export interface ConfigTemplateField {
  name: string;
  /** The value that the template suggests, e.g. `Fin 2`, or `_` for the user to fill in */
  value: string;
}

/** The JSON of `Veil.ConfigTemplate` */
export interface ConfigTemplate {
  module: string;
  /** The name that imports the file of the module; missing if no file can import it */
  import?: string | null;
  instantiation: ConfigTemplateField[];
  theory: ConfigTemplateField[];
}

/** A piece of a snippet: text as it is, or a placeholder that starts with some text */
export type SnippetPart = { text: string } | { placeholder: string };

/** What a config file for `template` starts with, before its command */
export function configHeader(template: ConfigTemplate): string {
  return `module\n\npublic import Veil\npublic import ${template.import}\n\n`;
}

/** The `#mc_config` command, from source arguments when given, else with template placeholders. */
export function configCommand(template: ConfigTemplate, source?: ModelCheckArguments): SnippetPart[] {
  if (source) return [{ text: `#mc_config ${template.module}\n` +
    [source.instantiation, ...(source.theory === undefined ? [] : [source.theory]), ...(source.options ?? [])]
      .map(term => term.split('\n').map(line => line === '' ? '' : `  ${line}`).join('\n')).join('\n') + '\n' }];
  const parts: SnippetPart[] = [{ text: `#mc_config ${template.module}` }];
  const structure = (fields: ConfigTemplateField[]) => {
    if (fields.length === 0) {
      parts.push({ text: '\n  {}' });
      return;
    }
    parts.push({ text: '\n  { ' });
    fields.forEach((field, i) => parts.push({ text: `${i > 0 ? ', ' : ''}${field.name} := ` }, { placeholder: field.value }));
    parts.push({ text: ' }' });
  };
  structure(template.instantiation);
  // `#mc_config` takes an empty theory when it is left out
  if (template.theory.length > 0) structure(template.theory);
  parts.push({ text: '\n' });
  return parts;
}

/** The text of `parts`, with each placeholder as it starts */
export function snippetText(parts: SnippetPart[]): string {
  return parts.map(part => 'text' in part ? part.text : part.placeholder).join('');
}

/** Where a new config file for the module of `moduleFile` goes: next to it, as TLC's model files go,
 * e.g. `PaxosMC.lean` for `Paxos.lean`, or `PaxosMC2.lean` for `index` 2 */
export function configFileFor(moduleFile: string, index = 1): string {
  return path.join(path.dirname(moduleFile), `${path.basename(moduleFile, '.lean')}MC${index > 1 ? index : ''}.lean`);
}

/** Whether the text of a config file imports `name`, so that configs of the modules of that file can
 * be added to it */
export function importsModule(text: string, name: string): boolean {
  const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  return new RegExp(`^[\\t ]*(?:(?:public|meta)\\s+)*import\\s+(?:all\\s+)?${escaped}(?=[\\t ]*(?:--|\\r?$))`, 'm').test(text);
}

/** The line breaks to add to `text` so that a command added at its end follows an empty line */
export function appendSeparator(text: string): string {
  if (text === '') return '';
  const lineBreaks = /(?:\r?\n)*$/.exec(text)![0].split('\n').length - 1;
  return '\n'.repeat(Math.max(0, 2 - lineBreaks));
}

/** Whether `#mc_config written` is of the module that `veil module declared` declares. The
 * command may name it with fewer namespaces than its declaration, or more. */
export function isOfModule(written: string, declared: string): boolean {
  const last = (name: string) => name.split('.').pop();
  return written === declared || last(written) === last(declared);
}
