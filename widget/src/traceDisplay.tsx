import * as React from 'react';
import { DocumentPosition } from '@leanprover/infoview';
import {
  ChangeInfo,
  diffChanges,
  CopyButton,
  formatActionLabel,
  renderValue,
  dequalify,
  sharedDiffCSS,
  sharedListCSS,
  generateFilterPanelCSS,
  generateJsonViewCSS,
  generateToggleLinkCSS,
  generateInstantiationCSS,
  mergeTheoryWithExtras,
  InstantiationRow,
} from './veilUtils';
import HtmlDisplay, { Html } from './htmlDisplay';


// ========== Types ==========
interface ParsedState {
  index: number;
  tag?: string; // Optional tag associated with this state (e.g. transition/action label)
  fields: Record<string, unknown>;
  failing?: boolean; // True if an assertion failed while executing the transition to this state
}
type Trace = ParsedState[];

type ViolationKind = "safety_failure" | "deadlock" | "assertion_failure";

interface AssertionInfo {
  procedureName: string;
  moduleName: string;
  line: number;
  column: number;
}

interface Violation {
  kind: ViolationKind;
  violates?: string[]; // Array of violated property names (only present for safety_failure)
  exception_id?: number; // Only present for assertion_failure
  assertion_info?: AssertionInfo; // Only present for assertion_failure
}

interface EarlyTerminationCondition {
  kind: "found_violating_state" | "deadlock_occurred" | "reached_depth_bound";
  depth?: number;
}

interface TerminationReason {
  kind: "explored_all_reachable_states" | "early_termination";
  condition?: EarlyTerminationCondition;
}

interface TraceData {
  theory: Record<string, unknown>;
  states: Array<{
    index: number;
    fields: Record<string, unknown>;
    transition: unknown;
    failing?: boolean;
  }>;
  instantiation?: Record<string, unknown>;
  extraVals?: Record<string, unknown>;
}

type ModelCheckingResult =
  | {
      result: "found_violation";
      violation: Violation;
      trace: TraceData | null;
    }
  | {
      result: "no_violation_found";
      explored_states: number;
      termination_reason: TerminationReason;
      trace?: TraceData | null;
    }
  | {
      result: "cancelled";
    }
  | {
      // Trace-only data without a result (for displaying execution traces)
      trace: TraceData;
    };

interface ModelCheckerViewProps {
  result: ModelCheckingResult;
  layout?: "vertical" | "horizontal";
  rawHtml?: Html;
}

/* ===================== Render ===================== */

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

const KVRow: React.FC<{
  k: string;
  v: unknown;
  changeInfo?: ChangeInfo;
  showRemovals?: boolean;
  onHideField?: (fieldName: string) => void;
}> = ({
  k,
  v,
  changeInfo,
  showRemovals = false,
  onHideField,
}) => {
  const collapsible = isCollapsibleValue(v);

  // Highlight the row if there's any change (array or full)
  const hasChange = changeInfo?.type === 'full' || changeInfo?.type === 'array';

  // Start expanded by default
  const [expanded, setExpanded] = React.useState(true);

  // For array changes, compute the merged view to pass to renderValue
  // If showRemovals is false, filter out removed elements from the merged view
  const mergedView = React.useMemo(() => {
    if (!expanded || changeInfo?.type !== 'array') return undefined;
    const view = changeInfo.mergedView;
    if (!showRemovals) {
      // Filter out removed elements when showRemovals is false
      return view.filter(m => m.status !== 'removed');
    }
    return view;
  }, [expanded, changeInfo, showRemovals]);

  return (
    <div
      className={`kv-row ${collapsible ? "has-toggle" : ""} ${
        hasChange ? "changed" : ""
      }`}
    >
      <div
        className={`kv-key ${onHideField ? 'kv-key-clickable' : ''}`}
        onClick={(e) => {
          if (onHideField && (e.altKey || e.metaKey)) {
            e.preventDefault();
            onHideField(k);
          }
        }}
        title={onHideField ? "Alt/Cmd-click to hide this field" : undefined}
      >
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
          {expanded ? renderValue(v, mergedView) : <code>{previewValue(v)}</code>}
        </div>
      </div>
    </div>
  );
};

const StateCard: React.FC<{
  st: ParsedState;
  highlighted?: boolean;
  changes?: Map<string, ChangeInfo>;
  showRemovals?: boolean;
  forceOpen?: boolean | null;  // null means use local state, true/false forces open/closed
  hiddenFields?: Set<string>;
  onHideField?: (fieldName: string) => void;
  onResetForceOpen?: () => void;  // Called when user clicks header while forceOpen is active
}> = ({ st, highlighted = false, changes, showRemovals = false, forceOpen = null, hiddenFields, onHideField, onResetForceOpen }) => {
  const isFailing = st.failing === true;
  const [localOpen, setLocalOpen] = React.useState(true);

  // Sync local state when forceOpen changes - this ensures that when we
  // reset to individual control, each state keeps the forced value
  React.useEffect(() => {
    if (forceOpen !== null) {
      setLocalOpen(forceOpen);
    }
  }, [forceOpen]);

  // Use forceOpen if set, otherwise use local state
  const open = forceOpen !== null ? forceOpen : localOpen;

  const handleHeaderClick = () => {
    if (forceOpen !== null && onResetForceOpen) {
      // User clicked while in force mode - switch to individual control
      // Set local state to opposite of current forced state, then reset force
      setLocalOpen(!forceOpen);
      onResetForceOpen();
    } else {
      setLocalOpen(o => !o);
    }
  };
  // Filter out hidden fields
  const entries = Object.entries(st.fields).filter(([k]) => !hiddenFields?.has(k));

  return (
    <div className={`state-card ${highlighted ? "is-highlighted" : ""} ${isFailing ? "is-failing" : ""}`}>
      <div className="state-header" onClick={handleHeaderClick}>
        <span className="action-chip" title={st.tag ?? ''}>
          {st.tag || '(no action)'}
        </span>
        {isFailing && <span className="failing-badge">FAILED</span>}
        <span className="state-id">(index: {st.index})</span>
        <div className="state-toggle">{open ? "▼" : "▶"}</div>
      </div>

      {open && (
        <div className="state-body">
          <div className="kv-table">
            {entries.map(([k, v]) => (
              <KVRow key={k} k={k} v={v} changeInfo={changes?.get(k)} showRemovals={showRemovals} onHideField={onHideField} />
            ))}
          </div>
        </div>
      )}
    </div>
  );
};

/** Collapsible section for displaying fields with a title */
const CollapsibleFieldsSection: React.FC<{
  title: string;
  fields: Record<string, unknown>;
  defaultExpanded?: boolean;
}> = ({ title, fields, defaultExpanded = false }) => {
  const [expanded, setExpanded] = React.useState(defaultExpanded);
  const entries = Object.entries(fields);

  return (
    <div className="theory-section">
      <div className="theory-header" onClick={() => setExpanded((e) => !e)}>
        <span className="theory-toggle">{expanded ? "▼" : "▶"}</span>
        <span className="theory-label">{title}</span>
      </div>
      {expanded && (
        <div className="theory-content">
          <div className="kv-table">
            {entries.map(([k, v]) => (
              <KVRow key={k} k={k} v={v} />
            ))}
          </div>
        </div>
      )}
    </div>
  );
};

/** Collapsible section for displaying theory info */
const TheorySection: React.FC<{ theory: Record<string, unknown> }> = ({ theory }) => {
  return <CollapsibleFieldsSection title="Theory" fields={theory} />;
};

/** Header showing the result status with appropriate icon */
const ResultHeader: React.FC<{
  resultType: "found_violation" | "no_violation_found" | "cancelled";
  violation?: Violation;
  exploredStates?: number;
  terminationReason?: TerminationReason;
}> = ({ resultType, violation, exploredStates, terminationReason }) => {
  if (resultType === "cancelled") {
    return (
      <div className="result-header result-cancelled">
        <span className="result-icon">⊘</span>
        <span className="result-label">Cancelled</span>
        <div className="result-details">
          Model checking was cancelled before completion
        </div>
      </div>
    );
  }

  if (resultType === "found_violation" && violation) {
    let icon: string;
    let label: string;
    switch (violation.kind) {
      case "deadlock":
        icon = "🔒";
        label = "Deadlock Detected";
        break;
      case "assertion_failure":
        icon = "💥";
        label = "Assertion Failed";
        break;
      default:
        icon = "⚠️";
        label = "Safety Violation Found";
    }
    return (
      <div className="result-header result-violation">
        <span className="result-icon">{icon}</span>
        <span className="result-label">{label}</span>
        {violation.kind === "safety_failure" && violation.violates && violation.violates.length > 0 && (
          <div className="result-details">
            <strong>Violated properties:</strong> {violation.violates.join(", ")}
          </div>
        )}
        {violation.kind === "assertion_failure" && violation.assertion_info && (
          <div className="result-details">
            <strong>Location:</strong> {violation.assertion_info.moduleName}.{violation.assertion_info.procedureName} (line {violation.assertion_info.line}, column {violation.assertion_info.column})
          </div>
        )}
      </div>
    );
  }

  // no_violation_found
  const getTerminationText = (reason: TerminationReason | undefined, count: number | undefined): string | null => {
    const countSuffix = count !== undefined ? ` (explored ${count} states)` : '';
    const countText = count !== undefined ? `Explored ${count} states` : null;

    if (!reason) return countText;
    if (reason.kind === "explored_all_reachable_states") {
      return count !== undefined ? `Explored all reachable states (${count})` : `Explored all reachable states`;
    }
    if (reason.kind === "early_termination" && reason.condition) {
      switch (reason.condition.kind) {
        case "found_violating_state":
          return `Stopped: found violating state${countSuffix}`;
        case "deadlock_occurred":
          return `Stopped: deadlock occurred${countSuffix}`;
        case "reached_depth_bound":
          return `Reached depth bound ${reason.condition.depth}${countSuffix}`;
        default:
          return `Early termination${countSuffix}`;
      }
    }
    return countText;
  };

  const terminationText = getTerminationText(terminationReason, exploredStates);

  return (
    <div className="result-header result-success">
      <span className="result-icon">✓</span>
      <span className="result-label">No Violation Found</span>
      {terminationText && (
        <div className="result-details">
          <span>{terminationText}</span>
        </div>
      )}
    </div>
  );
};

/** Helper to convert TraceData states to ParsedState format */
function traceDataToStates(traceData: TraceData): ParsedState[] {
  return traceData.states.map((st) => ({
    index: st.index,
    tag: formatActionLabel(st.transition),
    fields: st.fields,
    failing: st.failing,
  }));
}

const ModelCheckerView: React.FC<ModelCheckerViewProps> = ({
  result,
  layout = "vertical",
  rawHtml,
}) => {
  const isVertical = layout === "vertical";
  const [showRawJson, setShowRawJson] = React.useState(false);
  const [showRawModel, setShowRawModel] = React.useState(false);
  const [showRemovals, setShowRemovals] = React.useState(false);
  const [allStatesOpen, setAllStatesOpen] = React.useState<boolean | null>(null);  // null = individual control
  const [hiddenFields, setHiddenFields] = React.useState<Set<string>>(new Set());
  const [showFilterPanel, setShowFilterPanel] = React.useState(false);

  // Compute all unique field names from the trace
  const traceData = 'trace' in result ? result.trace : undefined;
  const allFieldNames = React.useMemo(() => {
    if (!traceData?.states) return [];
    const names = new Set<string>();
    for (const state of traceData.states) {
      for (const key of Object.keys(state.fields)) {
        names.add(key);
      }
    }
    return Array.from(names).sort();
  }, [traceData]);

  const toggleFieldVisibility = (fieldName: string) => {
    setHiddenFields(prev => {
      const next = new Set(prev);
      if (next.has(fieldName)) {
        next.delete(fieldName);
      } else {
        next.add(fieldName);
      }
      return next;
    });
  };

  const showAllFields = () => setHiddenFields(new Set());
  const hideAllFields = () => setHiddenFields(new Set(allFieldNames));

  // Keyboard shortcuts
  React.useEffect(() => {
    const handleKeyDown = (e: KeyboardEvent) => {
      // Handle Escape first - it should work everywhere to close the panel
      if (e.key === 'Escape') {
        setShowFilterPanel(false);
        return;
      }

      // Don't trigger other shortcuts when typing in an input field
      if (e.target instanceof HTMLInputElement || e.target instanceof HTMLTextAreaElement) {
        return;
      }
      // Only handle shortcuts when not in JSON view
      if (showRawJson) return;

      if (e.key === 'r' || e.key === 'R') {
        e.preventDefault();
        setShowRemovals(prev => !prev);
      } else if (e.key === 'c' || e.key === 'C') {
        e.preventDefault();
        setAllStatesOpen(prev => prev === false ? true : false);
      } else if (e.key === 'f' || e.key === 'F') {
        e.preventDefault();
        setShowFilterPanel(prev => !prev);
      }
    };

    document.addEventListener('keydown', handleKeyDown);
    return () => document.removeEventListener('keydown', handleKeyDown);
  }, [showRawJson]);

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
      background: var(--vscode-editorWidget-background);
      border: 1px solid var(--vscode-panel-border);
      border-radius: 4px;
      max-width: 720px;
    }
    .state-card {
      --border: var(--vscode-panel-border);
      --header: var(--vscode-editorGroupHeader-tabsBackground);
      --mono: ui-monospace, SFMono-Regular, Menlo, Consolas, "Liberation Mono", monospace;
      background: var(--vscode-editorWidget-background);
      border: 1px solid var(--border);
      border-radius: 6px;
      min-width: 320px;
      max-width: 720px;
      box-shadow: 0 1px 2px rgba(0,0,0,.08);
      overflow: hidden;
    }
    .state-card.is-highlighted {
      outline: 2px solid var(--vscode-editor-selectionHighlightBorder);
      box-shadow: 0 0 0 3px var(--vscode-editor-selectionBackground);
    }
    .state-card.is-failing {
      outline: 2px solid var(--vscode-inputValidation-errorBorder);
      box-shadow: 0 0 0 3px var(--vscode-inputValidation-errorBackground);
    }
    .state-card.is-failing .state-header {
      background: var(--vscode-inputValidation-errorBackground);
    }
    .failing-badge {
      display: inline-block;
      font-family: var(--mono);
      font-size: 10px;
      font-weight: 600;
      background: var(--vscode-inputValidation-errorBorder);
      color: var(--vscode-editor-background);
      border-radius: 3px;
      padding: 2px 6px;
      text-transform: uppercase;
      letter-spacing: 0.5px;
    }
    .state-header {
      background: var(--header);
      border-bottom: 1px solid var(--border);
      padding: 6px 10px;
      display: flex;
      align-items: center;
      gap: 8px;
      font-weight: 600;
      cursor: pointer;
    }
    .state-id {
      font-size: 12px;
      color: var(--vscode-descriptionForeground);
      margin-left: auto;
    }
    .state-toggle { font-size: 12px; color: var(--vscode-descriptionForeground); user-select: none; }
    .action-chip {
      display: inline-block;
      font-family: var(--mono);
      font-size: 11px;
      font-weight: normal;
      background: var(--vscode-activityBarBadge-background);
      color: var(--vscode-activityBarBadge-foreground);
      border: 1px solid var(--vscode-activityBarBadge-foreground);
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
      border-bottom: 1px solid var(--vscode-panel-border);
      background: var(--vscode-editor-background);
      transition: background-color .15s ease, border-left-color .15s ease;
      border-left: 3px solid transparent;
    }
    .kv-row:last-child { border-bottom: none; }
    .kv-row.changed {
      background: var(--vscode-editor-findMatchHighlightBackground);
      border-left: 3px solid var(--vscode-editor-findMatchHighlightBorder);
      color: var(--vscode-editor-foreground);
    }
    ${sharedDiffCSS}
    .kv-key {
      font-family: var(--mono);
      background: transparent;
      word-break: break-all;
      font-size: 11px;
    }
    .kv-sep { color: var(--vscode-descriptionForeground); background: transparent; }
    .kv-val {
      font-family: var(--mono);
      font-size: 11px;
      background: transparent;
      word-break: break-all;
      display: flex; align-items: flex-start; gap: 6px;
    }
    .kv-toggle {
      border: none; background: transparent; font-size: 12px; line-height: 1;
      cursor: pointer; color: var(--vscode-descriptionForeground); padding: 0 2px;
    }
    .kv-val.collapsed .kv-content code {
      white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 100%;
    }
    ${sharedListCSS}
    code {
      background: transparent;
      color: var(--vscode-foreground);
      padding: 2px 4px;
      border-radius: 3px;
      font-family: var(--mono);
    }
    .kv-val.collapsed .kv-content code {
      white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 100%;
    }
    .kv-content { display: block; }
    .action-chip { cursor: help; }
    .result-header {
      display: flex;
      align-items: center;
      gap: 8px;
      padding: 12px 16px;
      margin: 8px;
      border-radius: 6px;
      font-weight: 600;
      flex-wrap: wrap;
      max-width: 720px;
    }
    .result-violation {
      background: var(--vscode-inputValidation-errorBackground);
      border: 1px solid var(--vscode-inputValidation-errorBorder);
      color: var(--vscode-inputValidation-errorForeground, var(--vscode-foreground));
    }
    .result-success {
      background: var(--vscode-inputValidation-infoBackground);
      border: 1px solid var(--vscode-inputValidation-infoBorder);
      color: var(--vscode-inputValidation-infoForeground, var(--vscode-foreground));
    }
    .result-cancelled {
      background: var(--vscode-inputValidation-warningBackground);
      border: 1px solid var(--vscode-inputValidation-warningBorder);
      color: var(--vscode-inputValidation-warningForeground, var(--vscode-foreground));
    }
    .result-icon { font-size: 18px; }
    .result-label { font-size: 14px; }
    .result-details {
      width: 100%;
      font-size: 12px;
      font-weight: normal;
      color: var(--vscode-descriptionForeground);
      margin-top: 4px;
    }
    .theory-section {
      margin: 8px;
      border: 1px solid var(--vscode-panel-border);
      border-radius: 6px;
      background: var(--vscode-editorWidget-background);
      max-width: 720px;
    }
    .theory-header {
      display: flex;
      align-items: center;
      gap: 6px;
      padding: 8px 12px;
      cursor: pointer;
      font-weight: 600;
      font-size: 13px;
    }
    .theory-toggle {
      font-size: 12px;
      color: var(--vscode-descriptionForeground);
    }
    .theory-label {
      color: var(--vscode-foreground);
    }
    .theory-content {
      padding: 8px;
      border-top: 1px solid var(--vscode-panel-border);
    }
    .mc-toolbar {
      display: flex;
      justify-content: flex-end;
      gap: 12px;
      padding: 4px 8px;
      position: sticky;
      top: 0;
      z-index: 50;
      background: var(--vscode-editorWidget-background);
      border-bottom: 1px solid var(--vscode-panel-border);
    }
    ${generateToggleLinkCSS('mc')}
    ${generateFilterPanelCSS('mc')}
    ${generateInstantiationCSS('mc')}
    .mc-instantiation-row {
      max-width: 720px;
      margin-left: 8px;
      margin-right: 8px;
    }
    .kv-key-clickable {
      cursor: pointer;
    }
    .kv-key-clickable:hover {
      background: var(--vscode-list-hoverBackground);
      border-radius: 3px;
    }
    .mc-json-view {
      margin: 8px;
    }
    ${generateJsonViewCSS('mc')}
    .mc-raw-model {
      margin: 8px;
      padding: 12px;
      background: var(--vscode-editorWidget-background);
      border: 1px solid var(--vscode-panel-border);
      border-radius: 6px;
      overflow: auto;
      max-width: 720px;
    }
  `;

  const prettyJson = JSON.stringify(result, null, 2);

  // Extract trace and theory from results (works for all result types)
  const trace = traceData ? traceDataToStates(traceData) : [];

  // Merge theory with extraVals that have '.' in their names
  const { combinedTheory, remainingExtraVals } = React.useMemo(() => {
    if (!traceData?.theory) {
      return { combinedTheory: {}, remainingExtraVals: {} };
    }
    return mergeTheoryWithExtras(traceData.theory, traceData.extraVals);
  }, [traceData]);

  const instantiation = traceData?.instantiation;

  return (
    <>
      <style>{styles}</style>
      <div className="mc-root">
        <div className="mc-toolbar">
          {!showRawJson && !showRawModel && (
            <>
              <button
                className={`mc-toggle-link ${hiddenFields.size > 0 ? 'mc-filter-active' : ''}`}
                onClick={() => setShowFilterPanel(!showFilterPanel)}
                title="Filter visible fields (F)"
              >
                Filter fields {hiddenFields.size > 0 ? `(${hiddenFields.size} hidden)` : ''} (F)
              </button>
              <button className="mc-toggle-link" onClick={() => setAllStatesOpen(allStatesOpen === false ? true : false)} title="Keyboard shortcut: C">
                {allStatesOpen === false ? "Expand all (C)" : "Collapse all (C)"}
              </button>
              <button className="mc-toggle-link" onClick={() => setShowRemovals(!showRemovals)} title="Keyboard shortcut: R">
                {showRemovals ? "Hide removals (R)" : "Show removals (R)"}
              </button>
            </>
          )}
          {rawHtml && (
            <button className="mc-toggle-link" onClick={() => setShowRawModel(!showRawModel)}>
              {showRawModel ? "Show structured" : "Show raw model"}
            </button>
          )}
          <button className="mc-toggle-link" onClick={() => setShowRawJson(!showRawJson)}>
            {showRawJson ? "Show formatted" : "Show JSON"}
          </button>
        </div>

        {showRawJson ? (
          <div className="mc-json-view">
            <CopyButton text={prettyJson} className="mc-copy-button" />
            <div className="mc-json-content">
              {prettyJson}
            </div>
          </div>
        ) : showRawModel && rawHtml ? (
          <div className="mc-raw-model">
            <HtmlDisplay html={rawHtml} />
          </div>
        ) : (
          <>
            {'result' in result && (
              <>
                {result.result === "cancelled" ? (
                  <ResultHeader resultType="cancelled" />
                ) : result.result === "no_violation_found" ? (
                  <ResultHeader
                    resultType="no_violation_found"
                    exploredStates={result.explored_states}
                    terminationReason={result.termination_reason}
                  />
                ) : (
                  <ResultHeader
                    resultType="found_violation"
                    violation={result.violation}
                  />
                )}
              </>
            )}

            {instantiation && Object.keys(instantiation).length > 0 && (
              <InstantiationRow instantiation={instantiation} prefix="mc" />
            )}

            {Object.keys(combinedTheory).length > 0 && <TheorySection theory={combinedTheory} />}

            {trace.length > 0 ? (
              <>
                <div className={`mc-trace ${isVertical ? "vertical" : "horizontal"}`}>
                  {trace.map((s: ParsedState, idx: number) => {
                    const prev = idx > 0 ? trace[idx - 1].fields : undefined;
                    const changes = diffChanges(prev, s.fields);
                    return <StateCard key={s.index} st={s} changes={changes} showRemovals={showRemovals} forceOpen={allStatesOpen} hiddenFields={hiddenFields} onHideField={toggleFieldVisibility} onResetForceOpen={() => setAllStatesOpen(null)} />;
                  })}
                </div>

                {Object.keys(remainingExtraVals).length > 0 && (
                  <CollapsibleFieldsSection title="Extra Values" fields={remainingExtraVals} />
                )}

                <div className="mc-summary">
                  <strong>Summary:</strong> {trace.length} states in trace
                </div>
              </>
            ) : (
              'result' in result && result.result === "found_violation" && (
                <div className="mc-summary">
                  <strong>No trace available</strong>
                </div>
              )
            )}
          </>
        )}

        {/* Filter panel modal - rendered at root level for fixed positioning */}
        {showFilterPanel && (
          <>
            <div className="mc-filter-backdrop" onClick={() => setShowFilterPanel(false)} />
            <div className="mc-filter-panel">
              <div className="mc-filter-header">
                <span>Visible Fields</span>
                <div className="mc-filter-actions">
                  <button className="mc-filter-action" onClick={showAllFields}>Show all</button>
                  <button className="mc-filter-action" onClick={hideAllFields}>Hide all</button>
                  <button className="mc-filter-close" onClick={() => setShowFilterPanel(false)} title="Close (Esc)">×</button>
                </div>
              </div>
              <div className="mc-filter-list">
                {allFieldNames.map(name => (
                  <label key={name} className="mc-filter-item">
                    <input
                      type="checkbox"
                      checked={!hiddenFields.has(name)}
                      onChange={() => toggleFieldVisibility(name)}
                    />
                    <code>{name}</code>
                  </label>
                ))}
              </div>
            </div>
          </>
        )}
      </div>
    </>
  );
};

export default ModelCheckerView;
