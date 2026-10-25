// The `#model_check` commands of a Lean file, and their status from the messages that Lean
// reports for the file. This module does not use VS Code, so that the tests can run it.

/** The message that `#model_check` reports at the command once its binary is ready. */
export const BUILT_PREFIX = 'Model checker built: ';

const KEYWORD = '#model_check';

export interface BuildCommandSite {
  /** The 0-based position of `#model_check` */
  line: number;
  character: number;
  /** The last line of the command: the line before the next command, or before the next line that
   * starts at column 0 */
  endLine: number;
  /** The module that the command builds a model checker for */
  module: string;
  /** The text of the command, as `normalizeCommand` gives it */
  command: string;
}

/** `text` with its whitespace collapsed. This identifies a command while its file changes around
 * it, e.g. its line, and changes once the command does, e.g. its instantiation. */
export function normalizeCommand(text: string): string {
  return text.replace(/\s+/g, ' ').trim();
}

/** Where the code of a line starts: at its first character that is not whitespace, when that
 * character is in no comment or string */
interface CodeStart {
  line: number;
  character: number;
  offset: number;
}

/** The lines of `text` that start with code, and the offsets where all its lines start */
function scanLines(text: string): { starts: CodeStart[]; lineOffsets: number[] } {
  const starts: CodeStart[] = [];
  const lineOffsets = [0];
  let line = 0;
  let blockCommentDepth = 0;
  let inString = false;
  let inLineComment = false;
  // Whether the line has had a character that is not whitespace
  let started = false;
  for (let i = 0; i < text.length; i++) {
    const c = text[i];
    if (c === '\n') {
      line++;
      lineOffsets.push(i + 1);
      inLineComment = false;
      started = false;
      continue;
    }
    if (!started && !/\s/.test(c)) {
      started = true;
      if (blockCommentDepth === 0 && !inString) starts.push({ line, character: i - lineOffsets[line], offset: i });
    }
    if (inLineComment) continue;
    if (inString) {
      if (c === '\\' && text[i + 1] !== '\n') i++;
      else if (c === '"') inString = false;
      continue;
    }
    if (blockCommentDepth > 0) {
      if (c === '/' && text[i + 1] === '-') {
        blockCommentDepth++;
        i++;
      } else if (c === '-' && text[i + 1] === '/') {
        blockCommentDepth--;
        i++;
      }
      continue;
    }
    if (c === '-' && text[i + 1] === '-') {
      inLineComment = true;
    } else if (c === '/' && text[i + 1] === '-') {
      blockCommentDepth++;
      i++;
    } else if (c === '"') {
      inString = true;
    }
  }
  return { starts, lineOffsets };
}

/** Whether `word` is at `offset` in `text`, followed by whitespace or the end */
function wordAt(text: string, offset: number, word: string): boolean {
  return text.startsWith(word, offset) && /^\s?$/.test(text[offset + word.length] ?? '');
}

/** The `#model_check` commands in `text` that build a model checker, leaving out those in comments
 * and strings. As for Lean, these are the ones where an identifier follows the keyword, which names
 * the module, wherever they are. A command must start its line. */
export function findBuildCommands(text: string): BuildCommandSite[] {
  const { starts, lineOffsets } = scanLines(text);
  const lastLine = lineOffsets.length - 1;
  // The lines that start with code at column 0
  const topLevelLines = starts.filter(start => start.character === 0).map(start => start.line);
  const sites = starts.filter(start => wordAt(text, start.offset, KEYWORD)).map(start => {
    const name = /^\s+([\p{L}_«][^\s{}()[\]]*)/u.exec(text.slice(start.offset + KEYWORD.length, start.offset + KEYWORD.length + 1000));
    return { line: start.line, character: start.character, offset: start.offset, module: name ? name[1] : '' };
  }).filter(site => !['', '_', 'interpreted', 'compiled'].includes(site.module));
  return sites.map(({ offset, ...site }, i) => {
    const nextTopLevel = topLevelLines.find(l => l > site.line) ?? lastLine + 1;
    const nextSite = sites[i + 1]?.line ?? lastLine + 1;
    const endLine = Math.max(site.line, Math.min(nextTopLevel, nextSite) - 1);
    const command = normalizeCommand(text.slice(offset, lineOffsets[endLine + 1] ?? text.length));
    return { ...site, endLine, command };
  });
}

/** A `veil module` of a Lean file, with the lines of the commands of it that a config file needs */
export interface VeilModuleSite {
  /** The 0-based position of `veil module` */
  line: number;
  character: number;
  name: string;
  genSpecLine?: number;
  genExecutableLine?: number;
  /** The line of its `end`, if it has one */
  endLine?: number;
}

/** The `veil module`s in `text`, leaving out those in comments and strings */
export function findVeilModules(text: string): VeilModuleSite[] {
  const modules: VeilModuleSite[] = [];
  let open: VeilModuleSite | undefined;
  for (const start of scanLines(text).starts) {
    const rest = text.slice(start.offset, start.offset + 1000);
    const declared = /^veil\s+module\s+(\S+)/.exec(rest);
    if (declared) {
      open = { line: start.line, character: start.character, name: declared[1] };
      modules.push(open);
    } else if (open && wordAt(text, start.offset, '#gen_spec')) {
      open.genSpecLine ??= start.line;
    } else if (open && wordAt(text, start.offset, '#gen_executable')) {
      open.genExecutableLine ??= start.line;
    } else if (open && /^end\s+(\S+)/.exec(rest)?.[1] === open.name) {
      open.endLine = start.line;
      open = undefined;
    }
  }
  return modules;
}

export type Severity = 'error' | 'warning' | 'information' | 'hint';

/** A message that Lean reports for a file, as a diagnostic. */
export interface ReportedMessage {
  /** The 0-based line where the message starts */
  line: number;
  severity: Severity;
  message: string;
}

export type BuildStatus =
  | { kind: 'built'; binary: string }
  | { kind: 'failed'; message: string }
  | { kind: 'pending' };

/** Whether Lean has built the model checker of `site`, from the messages it reports for the file.
 * An error in the command means that the build was not done. */
export function buildStatus(site: BuildCommandSite, messages: ReportedMessage[]): BuildStatus {
  const inSite = messages.filter(m => m.line >= site.line && m.line <= site.endLine);
  const error = inSite.find(m => m.severity === 'error');
  if (error) return { kind: 'failed', message: error.message };
  const built = inSite.filter(m => m.severity === 'information' && m.message.startsWith(BUILT_PREFIX)).pop();
  if (built) return { kind: 'built', binary: built.message.slice(BUILT_PREFIX.length).trim() };
  return { kind: 'pending' };
}
