
import * as React from 'react';

// ========== Types ==========

/** Merged element for array diff display */
export interface MergedElement {
  element: unknown;
  status: 'unchanged' | 'added' | 'removed';
}

/** Value change info: either the whole value changed, or specific array indices changed */
export type ChangeInfo =
  | { type: 'full' }  // Entire value changed (non-array or structural change)
  | { type: 'array'; mergedView: MergedElement[] }  // Array with merged view showing elements in original order
  | { type: 'none' };  // No change

// ========== Diff Helpers ==========

/** Deep equality comparison for values */
export function deepEqual(a: unknown, b: unknown): boolean {
  if (a === b) return true;
  if (a == null || b == null) return a === b;

  if (Array.isArray(a) && Array.isArray(b)) {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
      if (!deepEqual(a[i], b[i])) return false;
    }
    return true;
  }

  if (typeof a === 'object' && typeof b === 'object') {
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

/**
 * Compute LCS (Longest Common Subsequence) using dynamic programming.
 * Returns array of [prevIndex, currIndex] pairs representing matched elements.
 */
function computeLCS(prev: unknown[], curr: unknown[]): [number, number][] {
  const m = prev.length;
  const n = curr.length;

  // Build DP table
  const dp: number[][] = Array.from({ length: m + 1 }, () => Array(n + 1).fill(0));

  for (let i = 1; i <= m; i++) {
    for (let j = 1; j <= n; j++) {
      if (deepEqual(prev[i - 1], curr[j - 1])) {
        dp[i][j] = dp[i - 1][j - 1] + 1;
      } else {
        dp[i][j] = Math.max(dp[i - 1][j], dp[i][j - 1]);
      }
    }
  }

  // Backtrack to find the LCS indices
  const lcs: [number, number][] = [];
  let i = m, j = n;
  while (i > 0 && j > 0) {
    if (deepEqual(prev[i - 1], curr[j - 1])) {
      lcs.unshift([i - 1, j - 1]);
      i--;
      j--;
    } else if (dp[i - 1][j] > dp[i][j - 1]) {
      i--;
    } else {
      j--;
    }
  }

  return lcs;
}

/**
 * Compute a merged view using LCS-based diff algorithm.
 * Additions and removals appear at their correct positions.
 */
export function computeMergedView(prev: unknown[], curr: unknown[]): MergedElement[] {
  const lcs = computeLCS(prev, curr);
  const result: MergedElement[] = [];

  let prevIdx = 0;
  let currIdx = 0;
  let lcsIdx = 0;

  while (prevIdx < prev.length || currIdx < curr.length) {
    const lcsMatch = lcsIdx < lcs.length ? lcs[lcsIdx] : null;

    if (lcsMatch && prevIdx === lcsMatch[0] && currIdx === lcsMatch[1]) {
      // This element is in the LCS - it's unchanged
      result.push({ element: curr[currIdx], status: 'unchanged' });
      prevIdx++;
      currIdx++;
      lcsIdx++;
    } else {
      // Not at an LCS match point - emit removals from prev, then additions from curr

      // Emit all removals up to the next LCS match (or end of prev)
      const nextPrevMatch = lcsMatch ? lcsMatch[0] : prev.length;
      while (prevIdx < nextPrevMatch) {
        result.push({ element: prev[prevIdx], status: 'removed' });
        prevIdx++;
      }

      // Emit all additions up to the next LCS match (or end of curr)
      const nextCurrMatch = lcsMatch ? lcsMatch[1] : curr.length;
      while (currIdx < nextCurrMatch) {
        result.push({ element: curr[currIdx], status: 'added' });
        currIdx++;
      }
    }
  }

  return result;
}

/** Compute change information for each field between prev and curr state */
export function diffChanges(
  prev: Record<string, unknown> | undefined | null,
  curr: Record<string, unknown>
): Map<string, ChangeInfo> {
  const changes = new Map<string, ChangeInfo>();
  if (!prev) return changes;

  const keys = new Set<string>([...Object.keys(prev), ...Object.keys(curr)]);
  for (const k of keys) {
    const hasA = k in prev;
    const hasB = k in curr;

    if (!hasA || !hasB) {
      changes.set(k, { type: 'full' });
      continue;
    }

    const prevVal = (prev as any)[k];
    const currVal = (curr as any)[k];

    if (deepEqual(prevVal, currVal)) {
      continue;
    }

    if (Array.isArray(prevVal) && Array.isArray(currVal)) {
      // Compute merged view with elements in original order
      const mergedView = computeMergedView(prevVal, currVal);
      // Only mark as changed if there are actual additions or removals
      const hasChanges = mergedView.some(m => m.status !== 'unchanged');
      if (hasChanges) {
        changes.set(k, { type: 'array', mergedView });
      }
    } else {
      changes.set(k, { type: 'full' });
    }
  }

  return changes;
}

// ========== React Helpers ==========

/** Concatenate React nodes with separator */
export function joinNodes(nodes: React.ReactNode[], sep: React.ReactNode = ', '): React.ReactNode {
  const out: React.ReactNode[] = [];
  nodes.forEach((n, i) => {
    out.push(<span key={`n-${i}`}>{n}</span>);
    if (i < nodes.length - 1) out.push(<span key={`s-${i}`}>{sep}</span>);
  });
  return <>{out}</>;
}

/** Copy button component */
export const CopyButton: React.FC<{ text: string; className?: string }> = ({ text, className }) => {
  const [copied, setCopied] = React.useState(false);

  const handleCopy = async () => {
    try {
      await navigator.clipboard.writeText(text);
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    } catch (err) {
      console.error('Failed to copy:', err);
    }
  };

  return (
    <button className={className} onClick={handleCopy} title="Copy to clipboard">
      <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2">
        {copied ? (
          <path d="M20 6L9 17l-5-5" strokeLinecap="round" strokeLinejoin="round" />
        ) : (
          <>
            <rect x="9" y="9" width="13" height="13" rx="2" ry="2" />
            <path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1" />
          </>
        )}
      </svg>
      {copied ? 'Copied!' : 'Copy JSON'}
    </button>
  );
};

// ========== String Helpers ==========

/** Remove namespace prefixes like A.B.C, keeping only the last segment */
export function dequalify(s: string): string {
  const parts = s.trim().split(/\s+/);

  const cleaned = parts
    .map((tok) => {
      let t = tok.replace(/^[()\[\]{}:,]+|[()\[\]{}:,]+$/g, "");
      if (/^-?\d+(?:\.\d+)?$/.test(t)) return t;
      if (t.includes(".")) {
        const segs = t.split(".");
        t = segs[segs.length - 1] || t;
      }
      return t;
    })
    .filter((t) => t.length > 0);

  return cleaned.join(" ");
}

/** Format an action/label object like {"recv": {"sender": 2}} into "recv(sender = 2)" */
export function formatActionLabel(label: unknown): string {
  if (typeof label === "string") {
    return label;
  }

  if (typeof label === "object" && label !== null) {
    const obj = label as Record<string, unknown>;
    const keys = Object.keys(obj);

    if (keys.length === 1) {
      let actionName = keys[0];
      if (actionName.startsWith("_")) {
        actionName = actionName.slice(1);
      }

      const args = obj[keys[0]];
      if (typeof args === "object" && args !== null && !Array.isArray(args)) {
        const argObj = args as Record<string, unknown>;
        const argKeys = Object.keys(argObj);
        if (argKeys.length > 0) {
          const formatValue = (v: unknown): string => {
            if (typeof v === "string") return v;
            if (typeof v === "number" || typeof v === "boolean") return String(v);
            return JSON.stringify(v);
          };
          const argStr = argKeys
            .map((k) => `${k} = ${formatValue(argObj[k])}`)
            .join(", ");
          return `${actionName}(${argStr})`;
        }
      }

      return actionName;
    }
  }

  return JSON.stringify(label);
}

// ========== Value Rendering ==========

/** Render any value inline (arrays as [a, b, ...]) */
export function renderValueInline(x: unknown): React.ReactNode {
  if (Array.isArray(x)) {
    const elements = x.map((el, i) => <span key={i}>{renderValueInline(el)}</span>);
    return <code>[{joinNodes(elements)}]</code>;
  }
  if (typeof x === 'object' && x !== null) {
    return <code>{JSON.stringify(x)}</code>;
  }
  if (typeof x === 'string') {
    return <code>{dequalify(x)}</code>;
  }
  return <code>{String(x)}</code>;
}

/** Render inline array using merged view for proper ordering */
export function renderInlineArrayMerged(mergedView: MergedElement[]): React.ReactNode {
  const parts: React.ReactNode[] = [];

  mergedView.forEach((item, i) => {
    const element = renderValueInline(item.element);
    const className = item.status === 'added' ? 'changed-element' : item.status === 'removed' ? 'removed-element' : undefined;
    parts.push(className ? <span key={i} className={className}>{element}</span> : <span key={i}>{element}</span>);
    if (i < mergedView.length - 1) parts.push(<span key={`comma-${i}`}>, </span>);
  });
  return <code>[{parts}]</code>;
}

/** Render inline array (when no diff info available) */
export function renderInlineArray(arr: unknown[]): React.ReactNode {
  const parts: React.ReactNode[] = [];
  arr.forEach((e, i) => {
    parts.push(<span key={i}>{renderValueInline(e)}</span>);
    if (i < arr.length - 1) parts.push(<span key={`comma-${i}`}>, </span>);
  });
  return <code>[{parts}]</code>;
}

/**
 * Render a row from an inner array:
 * - If it's a flat tuple (all elements are primitives), render as (a, b, c)
 * - Otherwise, render the inner array inline as [a, b, ...]
 */
export function renderRowFromInnerArray(e: unknown, status?: 'unchanged' | 'added' | 'removed'): React.ReactNode {
  const className = status === 'added' ? 'changed-element' : status === 'removed' ? 'removed-element' : undefined;

  if (Array.isArray(e)) {
    const isFlatTuple = e.every(el => !Array.isArray(el));
    if (isFlatTuple) {
      const parts: React.ReactNode[] = [];
      e.forEach((el, i) => {
        parts.push(renderValueInline(el));
        if (i < e.length - 1) parts.push(', ');
      });
      const code = <code>({parts})</code>;
      return className ? <span className={className}>{code}</span> : code;
    } else {
      const content = renderValueInline(e);
      return className ? <span className={className}>{content}</span> : content;
    }
  }
  return renderValue(e);
}

/** Render a value with optional diff highlighting via mergedView */
export function renderValue(v: unknown, mergedView?: MergedElement[]): React.ReactNode {
  if (Array.isArray(v)) {
    if (v.length === 0 && (!mergedView || mergedView.length === 0)) {
      return <code>[]</code>;
    }

    if (mergedView && mergedView.length > 0) {
      const hasInnerArray = mergedView.some(m => Array.isArray(m.element));

      if (hasInnerArray) {
        return (
          <ul className="list">
            {mergedView.map((item, i) => (
              <li key={i}>{renderRowFromInnerArray(item.element, item.status)}</li>
            ))}
          </ul>
        );
      }

      return renderInlineArrayMerged(mergedView);
    }

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

// ========== Shared CSS ==========

/** Shared CSS for diff highlighting (changed/removed elements) */
export const sharedDiffCSS = `
  .changed-element {
    background: var(--vscode-diffEditor-insertedTextBackground, rgba(0, 255, 0, 0.2));
    border-radius: 3px;
    padding: 2px 4px;
    box-shadow: 0 0 0 2px var(--vscode-diffEditor-insertedLineBackground, rgba(0, 255, 0, 0.3));
    color: var(--vscode-editor-foreground);
  }
  .removed-element {
    background: var(--vscode-diffEditor-removedTextBackground, rgba(255, 0, 0, 0.2));
    border-radius: 3px;
    padding: 2px 4px;
    box-shadow: 0 0 0 2px var(--vscode-diffEditor-removedLineBackground, rgba(255, 0, 0, 0.3));
    color: var(--vscode-editor-foreground);
    text-decoration: line-through;
    opacity: 0.8;
  }
`;

/** Shared CSS for list rendering */
export const sharedListCSS = `
  ul.list {
    margin: 4px 0 0 0;
    padding: 0;
    list-style: none;
  }
  ul.list li {
    font-family: var(--mono, ui-monospace, SFMono-Regular, Menlo, Consolas, "Liberation Mono", monospace);
    font-size: 11px;
    line-height: 1.4;
    background: transparent;
    color: var(--vscode-foreground);
    margin: 2px 0;
  }
`;

/** Generate filter panel CSS with a given prefix (e.g., 'mc' or 'cex') */
export function generateFilterPanelCSS(prefix: string): string {
  return `
  .${prefix}-filter-active {
    color: var(--vscode-notificationsInfoIcon-foreground, #3794ff);
    font-weight: 600;
  }
  .${prefix}-filter-panel {
    position: fixed;
    top: 50%;
    left: 50%;
    transform: translate(-50%, -50%);
    z-index: 1000;
    min-width: 250px;
    max-width: 90vw;
    max-height: 400px;
    background: var(--vscode-editorWidget-background);
    border: 1px solid var(--vscode-panel-border);
    border-radius: 8px;
    box-shadow: 0 8px 32px rgba(0, 0, 0, 0.3);
    overflow: hidden;
  }
  .${prefix}-filter-backdrop {
    position: fixed;
    top: 0;
    left: 0;
    right: 0;
    bottom: 0;
    background: rgba(0, 0, 0, 0.3);
    z-index: 999;
  }
  .${prefix}-filter-header {
    display: flex;
    justify-content: space-between;
    align-items: center;
    padding: 8px 12px;
    border-bottom: 1px solid var(--vscode-panel-border);
    font-weight: 600;
    font-size: 12px;
  }
  .${prefix}-filter-actions {
    display: flex;
    gap: 8px;
  }
  .${prefix}-filter-action {
    font-size: 10px;
    color: var(--vscode-textLink-foreground);
    background: none;
    border: none;
    cursor: pointer;
    padding: 2px 4px;
  }
  .${prefix}-filter-action:hover {
    text-decoration: underline;
  }
  .${prefix}-filter-close {
    font-size: 18px;
    line-height: 1;
    color: var(--vscode-foreground);
    background: none;
    border: none;
    cursor: pointer;
    padding: 0 4px;
    margin-left: 8px;
    opacity: 0.7;
  }
  .${prefix}-filter-close:hover {
    opacity: 1;
  }
  .${prefix}-filter-list {
    padding: 8px;
    max-height: 240px;
    overflow-y: auto;
  }
  .${prefix}-filter-item {
    display: flex;
    align-items: center;
    gap: 8px;
    padding: 4px;
    cursor: pointer;
    border-radius: 3px;
    font-size: 12px;
  }
  .${prefix}-filter-item:hover {
    background: var(--vscode-list-hoverBackground);
  }
  .${prefix}-filter-item input {
    margin: 0;
  }
  .${prefix}-filter-item code {
    font-size: 11px;
  }
`;
}

/** Generate JSON view CSS with a given prefix (e.g., 'mc' or 'vr') */
export function generateJsonViewCSS(prefix: string): string {
  return `
  .${prefix}-json-view {
    position: relative;
    background: var(--vscode-editor-background);
    border: 1px solid var(--vscode-panel-border);
    border-radius: 6px;
    max-height: 600px;
  }
  .${prefix}-json-content {
    padding: 12px;
    font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, "Liberation Mono", monospace;
    font-size: 12px;
    white-space: pre;
    overflow: auto;
    max-height: 600px;
  }
  .${prefix}-copy-button {
    position: absolute;
    top: 8px;
    right: 8px;
    display: inline-flex;
    align-items: center;
    gap: 4px;
    font-size: 11px;
    color: var(--vscode-button-foreground);
    background: var(--vscode-button-background);
    border: none;
    border-radius: 4px;
    padding: 4px 8px;
    cursor: pointer;
    transition: background 0.15s, opacity 0.15s;
    opacity: 0;
  }
  .${prefix}-json-view:hover .${prefix}-copy-button,
  .${prefix}-json-content:hover ~ .${prefix}-copy-button {
    opacity: 1;
  }
  .${prefix}-copy-button:hover {
    background: var(--vscode-button-hoverBackground);
  }
  .${prefix}-copy-button svg {
    width: 14px;
    height: 14px;
  }
`;
}

/** Generate toggle link CSS with a given prefix (e.g., 'mc' or 'vr') */
export function generateToggleLinkCSS(prefix: string): string {
  return `
  .${prefix}-toggle-link {
    font-size: 11px;
    color: var(--vscode-textLink-foreground);
    cursor: pointer;
    text-decoration: none;
    background: none;
    border: none;
    padding: 2px 6px;
    border-radius: 3px;
  }
  .${prefix}-toggle-link:hover {
    text-decoration: underline;
    background: var(--vscode-toolbar-hoverBackground);
  }
`;
}

/** Generate instantiation row CSS with a given prefix (e.g., 'mc' or 'cex') */
export function generateInstantiationCSS(prefix: string): string {
  return `
  .${prefix}-instantiation-row {
    display: flex;
    align-items: center;
    gap: 12px;
    margin-bottom: 12px;
    padding: 8px 12px;
    background: var(--vscode-editorWidget-background);
    border: 1px solid var(--vscode-panel-border);
    border-radius: 6px;
  }
  .${prefix}-instantiation-label {
    font-size: 10px;
    font-weight: 600;
    text-transform: uppercase;
    letter-spacing: 0.5px;
    color: var(--vscode-descriptionForeground);
    flex-shrink: 0;
  }
  .${prefix}-instantiation-values {
    display: flex;
    flex-wrap: wrap;
    gap: 8px;
  }
  .${prefix}-instantiation-item {
    display: inline-flex;
    align-items: center;
    gap: 4px;
    padding: 3px 10px;
    background: var(--vscode-activityBarBadge-background);
    color: var(--vscode-activityBarBadge-foreground);
    border-radius: 12px;
    font-size: 12px;
  }
  .${prefix}-instantiation-key {
    color: var(--vscode-activityBarBadge-foreground);
    font-weight: 500;
  }
  .${prefix}-instantiation-eq {
    color: var(--vscode-activityBarBadge-foreground);
    opacity: 0.6;
  }
  .${prefix}-instantiation-val {
    color: var(--vscode-activityBarBadge-foreground);
    font-weight: 500;
  }
`;
}

// ========== Extra Values Processing ==========

export interface SplitExtraValsResult {
  theoryExtras: Record<string, unknown>;
  remainingExtras: Record<string, unknown>;
}

/**
 * Split extraVals: items with '.' in name go to theory, others stay as extra values.
 * This is used to merge theory-related extraVals (like "tot.le") into the theory section.
 */
export function splitExtraVals(extraVals: Record<string, unknown> | undefined): SplitExtraValsResult {
  const theoryExtras: Record<string, unknown> = {};
  const remainingExtras: Record<string, unknown> = {};

  if (extraVals) {
    for (const [k, v] of Object.entries(extraVals)) {
      if (k.includes('.')) {
        theoryExtras[k] = v;
      } else {
        remainingExtras[k] = v;
      }
    }
  }

  return { theoryExtras, remainingExtras };
}

/**
 * Merge theory with extraVals that have '.' in their names.
 * Returns the combined theory and remaining extraVals.
 */
export function mergeTheoryWithExtras(
  theory: Record<string, unknown>,
  extraVals: Record<string, unknown> | undefined
): { combinedTheory: Record<string, unknown>; remainingExtraVals: Record<string, unknown> } {
  const { theoryExtras, remainingExtras } = splitExtraVals(extraVals);
  return {
    combinedTheory: { ...theory, ...theoryExtras },
    remainingExtraVals: remainingExtras,
  };
}

// ========== Instantiation Component ==========

export interface InstantiationRowProps {
  instantiation: Record<string, unknown>;
  prefix: string;
}

/** Reusable instantiation row component */
export const InstantiationRow: React.FC<InstantiationRowProps> = ({ instantiation, prefix }) => {
  if (!instantiation || Object.keys(instantiation).length === 0) {
    return null;
  }

  return (
    <div className={`${prefix}-instantiation-row`}>
      <span className={`${prefix}-instantiation-label`}>Instantiation</span>
      <div className={`${prefix}-instantiation-values`}>
        {Object.entries(instantiation).map(([k, v]) => (
          <span key={k} className={`${prefix}-instantiation-item`}>
            <span className={`${prefix}-instantiation-key`}>{k}</span>
            <span className={`${prefix}-instantiation-eq`}>=</span>
            <span className={`${prefix}-instantiation-val`}>{String(v)}</span>
          </span>
        ))}
      </div>
    </div>
  );
};
