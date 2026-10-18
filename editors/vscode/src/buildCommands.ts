// The `#model_check_build` commands of a Lean file, and their status from the messages that Lean
// reports for the file. This module does not use VS Code, so that the tests can run it.

/** The message that `#model_check_build` reports at the command once its binary is ready. */
export const BUILT_PREFIX = 'Model checker built: ';

const KEYWORD = '#model_check_build';

export interface BuildCommandSite {
  /** The 0-based position of `#model_check_build` */
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

/** The `#model_check_build` commands in `text`, leaving out those in comments and strings. A
 * command must start its line. */
export function findBuildCommands(text: string): BuildCommandSite[] {
  const sites: Omit<BuildCommandSite, 'endLine' | 'command'>[] = [];
  const lineStarts = [0];
  // The lines whose first character is code, i.e. not whitespace, a comment, or a string
  const topLevelLines: number[] = [];
  let line = 0;
  let lineStart = 0;
  let blockCommentDepth = 0;
  let inString = false;
  let inLineComment = false;
  let onlySpaceBefore = true;
  for (let i = 0; i < text.length; i++) {
    const c = text[i];
    if (c === '\n') {
      line++;
      lineStart = i + 1;
      lineStarts.push(lineStart);
      inLineComment = false;
      onlySpaceBefore = true;
      continue;
    }
    if (i === lineStart && blockCommentDepth === 0 && !inString && !/\s/.test(c)) topLevelLines.push(line);
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
      onlySpaceBefore = false;
    } else if (c === '"') {
      inString = true;
      onlySpaceBefore = false;
    } else if (onlySpaceBefore && text.startsWith(KEYWORD, i) && /^\s?$/.test(text[i + KEYWORD.length] ?? '')) {
      const name = /^\s+([^\s{}()[\]]+)/.exec(text.slice(i + KEYWORD.length, i + KEYWORD.length + 1000));
      sites.push({ line, character: i - lineStart, module: name ? name[1] : '' });
      onlySpaceBefore = false;
    } else if (!/\s/.test(c)) {
      onlySpaceBefore = false;
    }
  }
  return sites.map((site, i) => {
    const nextTopLevel = topLevelLines.find(l => l > site.line) ?? line + 1;
    const nextSite = sites[i + 1]?.line ?? line + 1;
    const endLine = Math.max(site.line, Math.min(nextTopLevel, nextSite) - 1);
    const command = normalizeCommand(text.slice(lineStarts[site.line] + site.character, lineStarts[endLine + 1] ?? text.length));
    return { ...site, endLine, command };
  });
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
