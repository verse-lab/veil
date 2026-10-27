// Source arguments of in-module checks, including checks kept as comments. Unlike #mc_config
// discovery, this deliberately reads comment bodies as well as code.
import { findVeilModules } from './buildCommands';

export interface ModelCheckArguments {
  /** Each term keeps the columns of its lines relative to each other, by which Lean reads some layouts,
   * e.g. fields separated by newlines: its least indented line starts at column 0. */
  instantiation: string;
  theory?: string;
  /** Options accepted by #mc_config, in their original order. */
  options?: string[];
}

export interface ModelCheckSite extends ModelCheckArguments {
  line: number;
  character: number;
  moduleLine: number;
}

/** Code, or the body of a comment */
interface Source {
  text: string;
  /** Where `text` starts in the file */
  offset: number;
  inComment: boolean;
}

/** The end of a string, raw string, quoted identifier, or character literal at `at`. In a comment,
 * where a quote may be prose, a literal must end on its line. */
function literalEnd(text: string, at: number, inComment: boolean): number | undefined {
  const newline = text.indexOf('\n', at);
  const limit = inComment && newline >= 0 ? newline : text.length;
  // In code, an unfinished literal runs to the end
  const unfinished = inComment ? undefined : text.length;
  const raw = /^r(#+)?"/.exec(text.slice(at));
  if (raw) {
    const end = text.indexOf(`"${raw[1] ?? ''}`, at + raw[0].length);
    return end < 0 || end >= limit ? unfinished : end + 1 + (raw[1]?.length ?? 0);
  }
  if (text[at] === '«') {
    const end = text.indexOf('»', at + 1);
    return end < 0 || end >= limit ? unfinished : end + 1;
  }
  if (text[at] === "'") {
    const char = /^'(?:\\(?:u\{[0-9a-fA-F]+\}|.)|[^'\\])'/u.exec(text.slice(at));
    if (char) return at + char[0].length;
  }
  if (text[at] !== '"') return undefined;
  for (let i = at + 1; i < limit; i++) {
    if (text[i] === '\\') i++;
    else if (text[i] === '"') return i + 1;
  }
  return unfinished;
}

/** Code with comments blanked, and each comment body treated recursively as another source.
 * Blanking preserves offsets and newlines, including the prefixes of consecutive `--` lines. */
function sources(text: string, offset = 0, inComment = false): Source[] {
  const code = text.split('');
  const comments: Source[] = [];
  for (let i = 0; i < text.length;) {
    const literal = literalEnd(text, i, inComment);
    if (literal !== undefined) { i = literal; continue; }
    const start = i;
    if (text.startsWith('--', i)) {
      const comment = /^--[^\n]*(?:\n[\t ]*--[^\n]*)*/.exec(text.slice(i))![0];
      comments.push(...sources(comment.replace(/(^|\n)([\t ]*)--/g, '$1$2  '), offset + i, true));
      i += comment.length;
    } else if (text.startsWith('/-', i)) {
      let depth = 1;
      i += 2;
      const body = i;
      while (i < text.length && depth > 0) {
        if (text.startsWith('/-', i)) { depth++; i += 2; }
        else if (text.startsWith('-/', i)) { depth--; i += 2; }
        else i++;
      }
      comments.push(...sources(text.slice(body, depth === 0 ? i - 2 : i), offset + body, true));
    } else {
      i++;
      continue;
    }
    for (let j = start; j < i; j++) if (code[j] !== '\n') code[j] = ' ';
  }
  return [{ text: code.join(''), offset, inComment }, ...comments];
}

/** Recognize delimited terms and names without splitting their expressions into fields.
 * This is source discovery, not a Lean parser; Lean still checks the generated config. */
function termAt(text: string, at: number, inComment: boolean): { term: string; start: number; end: number } | undefined {
  at += /^\s*/.exec(text.slice(at))![0].length;
  const closing: Record<string, string> = { '{': '}', '(': ')', '[': ']', '⟨': '⟩', '⦃': '⦄' };
  if (closing[text[at]]) {
    const stack: string[] = [];
    for (let i = at; i < text.length; i++) {
      const literal = literalEnd(text, i, inComment);
      if (literal !== undefined) { i = literal - 1; continue; }
      if (closing[text[i]]) stack.push(closing[text[i]]);
      else if (Object.values(closing).includes(text[i])) {
        if (stack.pop() !== text[i]) return undefined;
        if (stack.length === 0) return { term: text.slice(at, i + 1), start: at, end: i + 1 };
      }
      // Do not recover an unfinished term by consuming a later command, e.g. `#check`, unlike `#[1]`.
      if (text[i] === '\n' && /^\s*(?:#[\p{L}_][\p{L}\p{N}_]*(?![\p{L}\p{N}_\[])|end\b)/u.test(text.slice(i + 1))) return undefined;
    }
    return undefined;
  }
  const name = /^(?:«[^»]+»|[\p{L}_][\p{L}\p{N}_']*)(?:\.(?:«[^»]+»|[\p{L}_][\p{L}\p{N}_']*))*/u.exec(text.slice(at))?.[0];
  if (!name || /^(?:end|def|abbrev|theorem|example|instance|open|namespace|section|set_option|assumptions_hold_by|invariant|safety|termination|action|after_init|state_constraint|attribute|macro|syntax|by|do|let|if|match|fun|show|calc)$/.test(name)) return undefined;
  if (!/^(?:\s|[({]|$)/.test(text.slice(at + name.length))) return undefined;
  return { term: name, start: at, end: at + name.length };
}

/** Whether a term is a name, rather than a delimited term */
function isName(term: string): boolean {
  return /^[«\p{L}_]/u.test(term);
}

/** One Lean config item, including boolean shorthand and nested expressions in its value. */
function optionAt(text: string, at: number, inComment: boolean):
    { name: string; start: number; end: number; value?: { start: number; end: number } } | undefined {
  at += /^\s*/.exec(text.slice(at))![0].length;
  const rest = text.slice(at);
  const value = /^\(\s*(«[^»]+»|[\p{L}_][\p{L}\p{N}_'.]*)\s*:=\s*/u.exec(rest);
  if (value) {
    const term = termAt(text, at, inComment);
    if (!term) return undefined;
    // The value ends before the closing parenthesis, and the whitespace before it
    return { name: value[1].replace(/^«|»$/g, ''), start: at, end: term.end,
      value: { start: at + value[0].length, end: at + term.term.slice(0, -1).trimEnd().length } };
  }
  const flag = /^[+-](«[^»]+»|[\p{L}_][\p{L}\p{N}_'.]*)/u.exec(rest);
  return flag && { name: flag[1].replace(/^«|»$/g, ''), start: at, end: at + flag[0].length } || undefined;
}

/** `term`, whose first line starts at `column`, with its lines moved alike so that the least indented
 * one starts at column 0 */
function dedent(term: string, column: number): string {
  const lines = term.split('\n');
  const indent = (line: string) => /^[\t ]*/.exec(line)![0].length;
  const shift = Math.min(column, ...lines.slice(1).filter(line => line.trim() !== '').map(indent));
  return ' '.repeat(column - shift) +
    lines.map((line, i) => i === 0 ? line : line.trim() === '' ? '' : line.slice(shift)).join('\n');
}

/** The config item from `start` to `end` of `text`, whose `value` is copied with the runtime fields
 * reset. The copy moves the first line of the value right, so it moves its other lines alike. */
function withoutRuntimeFields(text: string, start: number, value: { start: number; end: number }, end: number): string {
  const prefix = '{ ((';
  return text.slice(start, value.start) + prefix +
    text.slice(value.start, value.end).replace(/\n/g, `\n${' '.repeat(prefix.length)}`) +
    ') : Veil.ModelCheckerConfig) with sequential := false, parallelCfg := none }' + text.slice(value.end, end);
}

/** Checks within a real `veil module`, at the start of a code or comment line. Each check gets
 * its own site, so a lens uses exactly the selected instantiation rather than a file-wide default.
 * The words of a comment are prose, so there the instantiation and the theory are delimited terms. */
export function findModelChecks(text: string): ModelCheckSite[] {
  const modules = findVeilModules(text);
  if (modules.length === 0 || !text.includes('#model_check')) return [];
  const sites: ModelCheckSite[] = [];
  for (const source of sources(text)) {
    const searchable = source.text.split('');
    for (let i = 0; i < source.text.length; i++) {
      const end = literalEnd(source.text, i, source.inComment);
      if (end === undefined) continue;
      for (let j = i; j < end; j++) if (searchable[j] !== '\n') searchable[j] = ' ';
      i = end - 1;
    }
    // The column in the file of `at` in the source, which may start within a line
    const column = (at: number) => source.offset + at - text.lastIndexOf('\n', source.offset + at - 1) - 1;
    const pattern = /^[\t ]*#model_check(?=\s|[({])/gm;
    for (const match of searchable.join('').matchAll(pattern)) {
      const local = match.index! + match[0].indexOf('#');
      const line = text.slice(0, source.offset + local).split('\n').length - 1;
      const module = modules.find(m => m.line < line && line < (m.endLine ?? Infinity));
      if (!module) continue;
      let at = local + '#model_check'.length;
      at += /^\s*(?:compiled|interpreted)\b/.exec(source.text.slice(at))?.[0].length ?? 0;
      const instantiation = termAt(source.text, at, source.inComment);
      if (!instantiation || source.inComment && isName(instantiation.term)) continue;
      const rest = source.text.slice(instantiation.end);
      if (rest.startsWith('.')) continue;
      // With the theory omitted, (field := value) is an option rather than a theory term.
      const startsOptions = optionAt(source.text, instantiation.end, source.inComment) !== undefined;
      let theory = startsOptions ? undefined : termAt(source.text, instantiation.end, source.inComment);
      // A name on a later line that is not indented past `#model_check` starts the next command,
      // e.g. `sat trace`, whose keywords are not known here.
      if (theory && isName(theory.term) && (source.inComment ||
          source.text.slice(instantiation.end, theory.start).includes('\n') && column(theory.start) <= column(local))) {
        theory = undefined;
      }
      if (!theory && /^\s*[{(]/.test(rest) && !startsOptions) continue;
      const options: string[] = [];
      let cursor = theory?.end ?? instantiation.end;
      for (;;) {
        const option = optionAt(source.text, cursor, source.inComment);
        if (!option) break;
        cursor = option.end;
        if (option.name === 'sequential' || option.name === 'parallelCfg') continue;
        // A full config may set runtime fields too, even indirectly through a named expression.
        // Clear only those fields, retaining maxDepth and any future checker settings.
        const written = option.name === 'config' && option.value && option.value.end > option.value.start
          ? withoutRuntimeFields(source.text, option.start, option.value, option.end)
          : source.text.slice(option.start, option.end);
        options.push(dedent(written, column(option.start)));
      }
      sites.push({ line, character: column(local), moduleLine: module.line,
        instantiation: dedent(instantiation.term, column(instantiation.start)),
        ...(theory ? { theory: dedent(theory.term, column(theory.start)) } : {}),
        ...(options.length > 0 ? { options } : {}) });
    }
  }
  return sites.sort((a, b) => a.line - b.line || a.character - b.character);
}
