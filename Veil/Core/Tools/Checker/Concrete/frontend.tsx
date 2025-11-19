import * as React from 'react';
import { DocumentPosition } from '@leanprover/infoview';


// ========== Types ==========
interface ParsedState {
  index: number;
  action?: string; // Optional action/tag associated with this state
  actionFull?: string;
  fields: Record<string, unknown>;
}
type Trace = ParsedState[];

interface ModelCheckerViewProps {
  trace: Trace;           // ← Directly pass the parsed JSON (ParsedState[])
  layout?: "vertical" | "horizontal";
}

/** Remove namespace prefixes like A.B.C, keeping only the last segment, e.g., "Mutex.states.start" -> "start" */
// function dequalify(s: string): string {
//   if (!s.includes(".") || /^-?\d+\.\d+$/.test(s)) return s; // Avoid misprocessing decimals
//   const parts = s.split(".");
//   return parts[parts.length - 1] || s;
// }
function dequalify(s: string): string {
  // First split by whitespace
  const parts = s.trim().split(/\s+/);

  const cleaned = parts
    .map((tok) => {
      // Remove surrounding parentheses/commas/etc.
      let t = tok.replace(/^[()\[\]{}:,]+|[()\[\]{}:,]+$/g, "");

      // Numbers (including decimals) are kept as is to avoid mis-splitting
      if (/^-?\d+(?:\.\d+)?$/.test(t)) return t;

      // Remove namespace prefixes for identifiers containing dots, keeping only the last segment
      if (t.includes(".")) {
        const segs = t.split(".");
        t = segs[segs.length - 1] || t;
      }

      return t;
    })
    // Remove potentially empty strings
    .filter((t) => t.length > 0);

  // Join back with spaces
  return cleaned.join(" ");
}


/* ================= Diff helpers: deepEqual + diffChangedKeys ================= */
function deepEqual(a: unknown, b: unknown): boolean {
  if (a === b) return true;
  if (a == null || b == null) return a === b;

  if (Array.isArray(a) && Array.isArray(b)) {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
      if (!deepEqual(a[i], b[i])) return false;
    }
    return true;
  }

  if (typeof a === "object" && typeof b === "object") {
    const ao = a as Record<string, unknown>;
    const bo = b as Record<string, unknown>;
    const ak = Object.keys(ao);
    const bk = Object.keys(bo);
    if (ak.length !== bk.length) return false;
    for (const k of ak) {
      if (!(k in bo)) return false;
      if (!deepEqual(ao[k], bo[k])) return false;
    }
    return true;
  }

  return false;
}

/** Compute the keys that have changed from prev to curr (including added, removed, or changed values) */
function diffChangedKeys(
  prev: Record<string, unknown> | undefined,
  curr: Record<string, unknown>
): Set<string> {
  const changed = new Set<string>();
  if (!prev) return changed; // No previous state for the first frame

  const keys = new Set<string>([...Object.keys(prev), ...Object.keys(curr)]);
  for (const k of keys) {
    const hasA = k in prev;
    const hasB = k in curr;
    if (!hasA || !hasB) {
      changed.add(k);
      continue;
    }
    if (!deepEqual((prev as any)[k], (curr as any)[k])) changed.add(k);
  }
  return changed;
}

/* ===================== Render ===================== */

/** Concatenate React node securely, without introducing extra whitespace */
function joinNodes(nodes: React.ReactNode[], sep: React.ReactNode = ', '): React.ReactNode {
  const out: React.ReactNode[] = [];
  nodes.forEach((n, i) => {
    out.push(<span key={`n-${i}`}>{n}</span>);
    if (i < nodes.length - 1) out.push(<span key={`s-${i}`}>{sep}</span>);
  });
  return <>{out}</>;
}

/** Render any value "inline" (arrays also inline as [a, b, ...], not converted to <ul>) */
function renderValueInline(x: unknown): React.ReactNode {
  if (Array.isArray(x)) {
    return <code>[{joinNodes(x.map(renderValueInline))}]</code>;
  }
  if (typeof x === 'object' && x !== null) {
    return <code>{JSON.stringify(x)}</code>;
  }
  if (typeof x === 'string') {
    return <code>{dequalify(x)}</code>;
  }
  return <code>{String(x)}</code>;
}


/** Render a row from an inner array:
 * - If it's length=2, render as `a, b` inline (no brackets)
 * - Otherwise, render the inner array inline as `[a, b, ...]`
 * If not an array, fallback to regular rendering
*/
function renderRowFromInnerArray(e: unknown): React.ReactNode {
  if (Array.isArray(e)) {
    if (e.length === 2) {
      const a = renderValueInline(e[0]);
      const b = renderValueInline(e[1]);
      return <code>({a}{', '}{b})</code>;      // ← Two elements in one line separated by a comma
    } else {
      return renderValueInline(e);           // ← Other lengths, inline as [ ... ]
    }
  }
  return renderValue(e);
}

/** Original: Inline rendering of flat arrays */
function renderInlineArray(arr: unknown[]): React.ReactNode {
  const parts: React.ReactNode[] = [];
  arr.forEach((e, i) => {
    parts.push(renderValueInline(e));        // Use inline version to avoid converting to <ul>
    if (i < arr.length - 1) parts.push(<span key={`comma-${i}`}>, </span>);
  });
  return <code>[{parts}]</code>;
}

function renderValue(v: unknown): React.ReactNode {
  if (Array.isArray(v)) {
    if (v.length === 0) return <code>[]</code>;

    // (a, b) single tuple: keep inline with parentheses
    const isTuple2 =
      v.length === 2 &&
      !Array.isArray(v[0]) &&
      !Array.isArray(v[1]);
    if (isTuple2) {
      const a = renderValue(v[0]);
      const b = renderValue(v[1]);
      return <code>({a},{' '}{b})</code>;
    }

    // ★ Key rule: As long as the "first-level list contains array elements", render each inner array on a separate line, but inline within the line
    const hasInnerArray = v.some(Array.isArray);
    if (hasInnerArray) {
      return (
        <ul className="list">
          {v.map((e, i) => (
            <li key={i}>{renderRowFromInnerArray(e)}</li>
          ))}
        </ul>
      );
    }

    // Inline to [a, b, c]
    return renderInlineArray(v);
  }

  if (typeof v === 'object' && v !== null) {
    return <code>{JSON.stringify(v)}</code>;
  }

  if (typeof v === 'string') {
    return <code>{dequalify(v)}</code>;
  }

  return <code>{String(v)}</code>;
}



// function isSimpleArray(arr: unknown[]): boolean {
//   if (arr.length <= 6) {
//     return arr.every(
//       (e) =>
//         e == null ||
//         typeof e === "string" ||
//         typeof e === "number" ||
//         typeof e === "boolean" ||
//         (Array.isArray(e) &&
//           e.every(
//             (x) =>
//               x == null ||
//               typeof x === "string" ||
//               typeof x === "number" ||
//               typeof x === "boolean"
//           ))
//     );
//   }
//   return false;
// }

// function renderInlineArray(arr: unknown[]): React.ReactNode {
//   const parts: React.ReactNode[] = [];
//   arr.forEach((e, i) => {
//     parts.push(renderValue(e));
//     if (i < arr.length - 1) parts.push(<span key={`comma-${i}`}>, </span>);
//   });
//   return <code>[{parts}]</code>;
// }


// function renderValue(v: unknown): React.ReactNode {
//   if (Array.isArray(v)) {
//     if (v.length === 0) return <code>[]</code>;

//     const isTuple2 =
//       v.length === 2 &&
//       v.every((x) => typeof x !== "object" || x == null || Array.isArray(x));
//     if (isTuple2) {
//       return (
//         <code>
//           ({renderValue(v[0])}, {renderValue(v[1])})
//         </code>
//       );
//     }

//     if (isSimpleArray(v)) {
//       return renderInlineArray(v);
//     }

//     return (
//       <ul className="list">
//         {v.map((e, i) => (
//           <li key={i}>{renderValue(e)}</li>
//         ))}
//       </ul>
//     );
//   }

//   if (typeof v === "object" && v !== null) {
//     return <code>{JSON.stringify(v)}</code>;
//   }

//   if (typeof v === "string") {
//     return <code>{dequalify(v)}</code>;
//   }

//   return <code>{String(v)}</code>;
// }

function isCollapsibleValue(v: unknown): boolean {
  if (Array.isArray(v)) return true;
  if (typeof v === "object" && v !== null) return true;
  if (typeof v === "string" && (v.includes("\n") || v.length > 60)) return true;
  return false;
}

function previewValue(v: unknown): string {
  if (Array.isArray(v)) {
    if (v.length > 0 && Array.isArray(v[0])) {
      return `Array(${v.length}) of tuples`;
    }
    return `Array(${v.length})`;
  }
  if (typeof v === "object" && v !== null) {
    try {
      return JSON.stringify(v).slice(0, 80) + "…";
    } catch {
      return "[object]";
    }
  }
  if (typeof v === "string") {
    const dq = dequalify(v);
    const s = dq.replace(/\s+/g, " ");
    return s.length > 80 ? s.slice(0, 80) + "…" : s;
  }
  return String(v);
}

const KVRow: React.FC<{ k: string; v: unknown; changed?: boolean }> = ({
  k,
  v,
  changed,
}) => {
  const collapsible = isCollapsibleValue(v);
  const [expanded, setExpanded] = React.useState(!collapsible);

  return (
    <div
      className={`kv-row ${collapsible ? "has-toggle" : ""} ${
        changed ? "changed" : ""
      }`}
    >
      <div className="kv-key">
        <code>{k}</code>
      </div>
      <div className="kv-sep">↦</div>

      <div className={`kv-val ${expanded ? "expanded" : "collapsed"}`}>
        {collapsible && (
          <button
            className="kv-toggle"
            type="button"
            onClick={() => setExpanded((e) => !e)}
            aria-label={expanded ? "Collapse value" : "Expand value"}
            title={expanded ? "Collapse" : "Expand"}
          >
            {expanded ? "▼" : "▶"}
          </button>
        )}

        <div className="kv-content">
          {expanded ? renderValue(v) : <code>{previewValue(v)}</code>}
        </div>
      </div>
    </div>
  );
};

const StateCard: React.FC<{
  st: ParsedState;
  highlighted?: boolean;
  changedKeys?: Set<string>;
}> = ({ st, highlighted = false, changedKeys }) => {
  const [open, setOpen] = React.useState(true);
  const entries = Object.entries(st.fields);

  return (
    <div className={`state-card ${highlighted ? "is-highlighted" : ""}`}>
      <div className="state-header" onClick={() => setOpen((o) => !o)}>
        <div className="state-title">
          {/* <span className="action-chip" title={st.actionFull ?? st.actionFull}>
            {st.action ? dequalify(st.action) : "(no action)"}{" "}
          </span> */}
          <span className="action-chip" title={st.actionFull ?? st.action ?? ''}>
            {st.action ? dequalify(st.action) : '(no action)'}
          </span>
          <span className="state-id">(index: {st.index})</span>
        </div>
        <div className="state-toggle">{open ? "▼" : "▶"}</div>
      </div>

      {open && (
        <div className="state-body">
          <div className="kv-table">
            {entries.map(([k, v]) => (
              <KVRow key={k} k={k} v={v} changed={changedKeys?.has(k)} />
            ))}
          </div>
        </div>
      )}
    </div>
  );
};

const ModelCheckerView: React.FC<ModelCheckerViewProps> = ({
  trace,
  layout = "vertical",
}) => {
  const isVertical = layout === "vertical";

  const styles = `
    .mc-root {
      font-family: system-ui, -apple-system, sans-serif;
      max-width: 100%;
      overflow: auto;
    }
    .mc-trace.vertical {
      display: flex;
      flex-direction: column;
      gap: 8px;
      padding: 8px;
    }
    .mc-trace.horizontal {
      display: flex;
      flex-direction: row;
      gap: 8px;
      padding: 8px;
      overflow-x: auto;
    }
    .mc-summary {
      margin: 12px 8px;
      padding: 8px 12px;
      background: #f8f9fa;
      border: 1px solid #dee2e6;
      border-radius: 4px;
    }
    .state-card {
      --border: #bfbfbf;
      --header: #e6e6e6;
      --mono: ui-monospace, SFMono-Regular, Menlo, Consolas, "Liberation Mono", monospace;
      background: #fff;
      border: 1px solid var(--border);
      border-radius: 6px;
      min-width: 320px;
      max-width: 720px;
      box-shadow: 0 1px 2px rgba(0,0,0,.08);
      overflow: hidden;
    }
    .state-card.is-highlighted {
      outline: 2px solid #ffc107;
      box-shadow: 0 0 0 3px rgba(255,193,7,.25);
    }
    .state-header {
      background: var(--header);
      border-bottom: 1px solid var(--border);
      padding: 6px 10px;
      display: flex;
      align-items: center;
      justify-content: space-between;
      font-weight: 600;
      cursor: pointer;
    }
    .state-title {
      display: flex;
      gap: 6px;
      align-items: baseline;
    }
    .state-id { font-size: 12px; color: #666; }
    .state-toggle { font-size: 12px; color: #666; user-select: none; }
    .action-chip {
      display: inline-block;
      font-family: var(--mono);
      font-size: 11px;
      font-weight: normal;
      background: #eaf2ff;
      color: #3b3b3dff;
      border: 1px solid #a9c3feff;
      border-radius: 999px;
      padding: 2px 8px;
      line-height: 1.4;
    }
    .state-body { padding: 10px; }
    .kv-table {
      border: 1px solid var(--border);
      border-radius: 4px;
      overflow: hidden;
    }
    .kv-row {
      display: grid;
      grid-template-columns: 1fr auto 2fr;
      gap: 8px;
      padding: 4px 10px;
      align-items: baseline;
      border-bottom: 1px solid #eee;
      background: white;
      transition: background-color .15s ease, border-left-color .15s ease;
      border-left: 3px solid transparent;
    }
    .kv-row:last-child { border-bottom: none; }
    .kv-row.changed {
      background: #fff7e6;
      border-left: 3px solid #faad14;
    }
    .kv-row.changed code { background: #fff1d6; }
    .kv-key {
      font-family: var(--mono);
      background: transparent;
      word-break: break-all;
      font-size: 11px;
    }
    .kv-sep { color: #888; background: transparent; }
    .kv-val {
      font-family: var(--mono);
      font-size: 11px;
      background: transparent;
      word-break: break-all;
      display: flex; align-items: flex-start; gap: 6px;
    }
    .kv-toggle {
      border: none; background: transparent; font-size: 12px; line-height: 1;
      cursor: pointer; color: #666; padding: 0 2px;
    }
    .kv-val.collapsed .kv-content code {
      white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 100%;
    }
    // .kv-content { display: block; }
    ul.list {
      margin: 4px 0 0 1rem;
      padding: 0;
      list-style-position: outside;
    }
    ul.list li {
      font-family: var(--mono);
      font-size: 11px;
      line-height: 1.4;
      background: transparent;
      color: #333;
      margin: 2px 0;
    }
    code {
      background: transparent;
      color: #333;
      padding: 2px 4px;
      border-radius: 3px;
      font-family: var(--mono);
    }
    .kv-val.collapsed .kv-content code {
      white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 100%;
    }
    .kv-content { display: block; }
    .action-chip { cursor: help; }
  `;

  return (
    <>
      <style>{styles}</style>
      <div className="mc-root">
        <div className={`mc-trace ${isVertical ? "vertical" : "horizontal"}`}>
          {trace.map((s, idx) => {
            const prev = idx > 0 ? trace[idx - 1].fields : undefined;
            const changed = diffChangedKeys(prev, s.fields);
            return <StateCard key={s.index} st={s} changedKeys={changed} />;
          })}
        </div>

        <div className="mc-summary">
          <strong>Summary:</strong> {trace.length} states
        </div>
      </div>
    </>
  );
};

export default ModelCheckerView;
