import * as React from 'react';
import { EditorContext } from '@leanprover/infoview';
import HtmlDisplay, { Html } from './htmlDisplay';
import {
  ChangeInfo,
  diffChanges,
  CopyButton,
  formatActionLabel,
  renderValue,
  sharedDiffCSS,
  sharedListCSS,
  generateFilterPanelCSS,
  generateJsonViewCSS,
  generateToggleLinkCSS,
  generateInstantiationCSS,
  mergeTheoryWithExtras,
  InstantiationRow,
} from './veilUtils';

// ========== Types ==========

interface InductionMetadataData {
  stmtDerivedFrom?: string[];
  property: string;
  kind?: 'primary' | 'alternative';
  action: string;
  style?: 'wp' | 'tr';
}

interface TraceMetadataData {
  traceName: string;
  numTransitions: number;
  isExpectedSat: boolean;
}

interface VCMetadata {
  type: 'induction' | 'trace';
  data: InductionMetadataData | TraceMetadataData;
}

interface StructuredJson {
  theory: Record<string, unknown>;
  preState: Record<string, unknown>;
  postState: Record<string, unknown> | null;
  label: Record<string, unknown>;
  instantiation: Record<string, unknown>;
  extraVals?: Record<string, unknown>;
  extraSorts?: Record<string, unknown>;
}

interface Counterexample {
  model?: any;
  structuredJson?: StructuredJson;
  html: Html | string;  // Can be either structured Html or raw HTML string
}

interface DischargerResultData {
  kind: string;
  counterexamples?: Counterexample[];
}

interface DischargerResult {
  time: number;
  status: string;
  data?: DischargerResultData;
  exceptions?: string[];
}

interface DischargerStatusFinished {
  finished: {
    res: DischargerResult;
  };
}

type DischargerStatus = string | DischargerStatusFinished;

interface Discharger {
  id: number;
  name: string;
  status: DischargerStatus;
  time: number | null;
  startTime: number | null;
  result?: DischargerResult | null;
}

interface VCTiming {
  totalTime: number | null;
  successfulDischargerTime?: number;
  successfulDischargerId?: number;
  dischargers: Discharger[];
}

interface VerificationCondition {
  id: number;
  name: string;
  status: 'proven' | 'disproven' | 'unknown' | 'error' | null;
  metadata: VCMetadata;
  timing: VCTiming;
  alternativeFor?: number | null;
  isDormant?: boolean;
  /** Theorem text for inserting into the editor (only for non-proven VCs) */
  theoremText?: string | null;
}

interface VerificationResults {
  vcs: VerificationCondition[];
  totalVCs: number;
  totalSolved: number;
  totalDischarged: number;
  serverTime: number;
}

interface InsertPosition {
  line: number;
  character: number;
}

interface VerificationResultsProps {
  results: VerificationResults;
  /** Position after #check_invariants for theorem insertion */
  insertPosition: InsertPosition;
  /** Document URI for edit operations */
  documentUri: string;
}

type StatusFilter = 'all' | 'proven' | 'disproven' | 'unknown' | 'error' | 'pending';

// ========== Helpers ==========

/** Key-value row component for state display */
const CexKVRow: React.FC<{
  k: string;
  v: unknown;
  changeInfo?: ChangeInfo;
}> = ({ k, v, changeInfo }) => {
  const hasChange = changeInfo?.type === 'full' || changeInfo?.type === 'array';
  const mergedView = changeInfo?.type === 'array' ? changeInfo.mergedView : undefined;

  return (
    <div className={`cex-kv-row ${hasChange ? 'changed' : ''}`}>
      <div className="cex-kv-key"><code>{k}</code></div>
      <div className="cex-kv-sep">↦</div>
      <div className="cex-kv-val">
        {renderValue(v, mergedView)}
      </div>
    </div>
  );
};

/** State panel component showing fields in a card */
const StatePanel: React.FC<{
  title: string;
  fields: Record<string, unknown>;
  changes?: Map<string, ChangeInfo>;
  statusIndicator?: React.ReactNode;
}> = ({ title, fields, changes, statusIndicator }) => {
  const entries = Object.entries(fields);

  return (
    <div className="cex-state-panel">
      <div className="cex-state-header">
        <span>{title}</span>
        {statusIndicator && (
          <span className="cex-state-status">{statusIndicator}</span>
        )}
      </div>
      <div className="cex-state-body">
        {entries.length === 0 ? (
          <div className="cex-empty-state">No fields</div>
        ) : (
          <div className="cex-kv-table">
            {entries.map(([k, v]) => (
              <CexKVRow key={k} k={k} v={v} changeInfo={changes?.get(k)} />
            ))}
          </div>
        )}
      </div>
    </div>
  );
};

/** Collapsible panel component for displaying fields */
const CollapsibleFieldsPanel: React.FC<{
  title: string;
  fields: Record<string, unknown>;
  defaultExpanded?: boolean;
}> = ({ title, fields, defaultExpanded = false }) => {
  const [expanded, setExpanded] = React.useState(defaultExpanded);
  const entries = Object.entries(fields);

  return (
    <div className="cex-theory-panel">
      <div
        className="cex-theory-header"
        onClick={() => setExpanded(!expanded)}
      >
        <span className="cex-theory-toggle">{expanded ? '▼' : '▶'}</span>
        <span className="cex-theory-label">{title}</span>
        <span className="cex-theory-count">({entries.length} {entries.length === 1 ? 'field' : 'fields'})</span>
      </div>
      {expanded && (
        <div className="cex-theory-body">
          {entries.length === 0 ? (
            <div className="cex-empty-state">No fields</div>
          ) : (
            <div className="cex-kv-table">
              {entries.map(([k, v]) => (
                <CexKVRow key={k} k={k} v={v} />
              ))}
            </div>
          )}
        </div>
      )}
    </div>
  );
};

/** Structured counterexample view with side-by-side pre/post states */
const StructuredCexView: React.FC<{
  data: StructuredJson;
  property: string;
  headerRightContent?: React.ReactNode;
}> = ({ data, property, headerRightContent }) => {
  const { theory, preState, postState, label, instantiation, extraVals } = data;

  // State for toolbar features
  const [showRemovals, setShowRemovals] = React.useState(false);
  const [hiddenFields, setHiddenFields] = React.useState<Set<string>>(new Set());
  const [showFilterPanel, setShowFilterPanel] = React.useState(false);
  const [isWideEnough, setIsWideEnough] = React.useState(true);
  const containerRef = React.useRef<HTMLDivElement>(null);

  // Detect when container is too narrow for side-by-side layout
  React.useEffect(() => {
    const container = containerRef.current;
    if (!container) return;

    const observer = new ResizeObserver((entries) => {
      for (const entry of entries) {
        // Stack panels vertically when width < 600px
        setIsWideEnough(entry.contentRect.width >= 600);
      }
    });

    observer.observe(container);
    return () => observer.disconnect();
  }, []);

  // Compute all unique field names from pre and post state
  const allFieldNames = React.useMemo(() => {
    const names = new Set<string>();
    for (const key of Object.keys(preState)) names.add(key);
    if (postState) {
      for (const key of Object.keys(postState)) names.add(key);
    }
    return Array.from(names).sort();
  }, [preState, postState]);

  // Compute diff from preState to postState
  const changes = postState ? diffChanges(preState, postState) : new Map<string, ChangeInfo>();

  // Filter fields based on hiddenFields
  const filteredPreState = React.useMemo(() => {
    const filtered: Record<string, unknown> = {};
    for (const [k, v] of Object.entries(preState)) {
      if (!hiddenFields.has(k)) filtered[k] = v;
    }
    return filtered;
  }, [preState, hiddenFields]);

  const filteredPostState = React.useMemo(() => {
    if (!postState) return null;
    const filtered: Record<string, unknown> = {};
    for (const [k, v] of Object.entries(postState)) {
      if (!hiddenFields.has(k)) filtered[k] = v;
    }
    return filtered;
  }, [postState, hiddenFields]);

  // Filter changes to only include visible fields, and optionally hide removals
  const filteredChanges = React.useMemo(() => {
    const filtered = new Map<string, ChangeInfo>();
    for (const [k, info] of changes) {
      if (hiddenFields.has(k)) continue;
      if (!showRemovals && info.type === 'array') {
        // Filter out removed elements when showRemovals is false
        const filteredMergedView = info.mergedView.filter(m => m.status !== 'removed');
        filtered.set(k, { type: 'array', mergedView: filteredMergedView });
      } else {
        filtered.set(k, info);
      }
    }
    return filtered;
  }, [changes, hiddenFields, showRemovals]);

  // Merge theory with extraVals that have '.' in their names
  const { combinedTheory, remainingExtraVals } = React.useMemo(
    () => mergeTheoryWithExtras(theory, extraVals),
    [theory, extraVals]
  );

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
      if (e.key === 'Escape') {
        setShowFilterPanel(false);
        return;
      }

      if (e.target instanceof HTMLInputElement || e.target instanceof HTMLTextAreaElement) {
        return;
      }

      if (e.key === 'r' || e.key === 'R') {
        e.preventDefault();
        setShowRemovals(prev => !prev);
      } else if (e.key === 'f' || e.key === 'F') {
        e.preventDefault();
        setShowFilterPanel(prev => !prev);
      }
    };

    document.addEventListener('keydown', handleKeyDown);
    return () => document.removeEventListener('keydown', handleKeyDown);
  }, []);

  return (
    <div className="cex-structured-view" ref={containerRef}>
      {/* Combined header with toolbar and controls */}
      <div className="cex-header-row">
        <div className="cex-header-left">
          <span className="cex-header-label">Counterexample</span>
          <button
            className={`cex-toolbar-btn ${hiddenFields.size > 0 ? 'cex-filter-active' : ''}`}
            onClick={(e) => { e.stopPropagation(); setShowFilterPanel(!showFilterPanel); }}
            title="Filter visible fields (F)"
          >
            Filter fields {hiddenFields.size > 0 ? `(${hiddenFields.size} hidden)` : ''} (F)
          </button>
          <button
            className="cex-toolbar-btn"
            onClick={(e) => { e.stopPropagation(); setShowRemovals(!showRemovals); }}
            title="Show/hide removed elements (R)"
          >
            {showRemovals ? "Hide removals (R)" : "Show removals (R)"}
          </button>
        </div>
        {headerRightContent && (
          <div className="cex-header-right">
            {headerRightContent}
          </div>
        )}
      </div>

      {/* Instantiation */}
      {instantiation && Object.keys(instantiation).length > 0 && (
        <InstantiationRow instantiation={instantiation} prefix="cex" />
      )}

      {/* Theory (collapsible, expanded by default) */}
      {Object.keys(combinedTheory).length > 0 && (
        <CollapsibleFieldsPanel title="Theory" fields={combinedTheory} defaultExpanded={true} />
      )}

      {/* Centered action chip above panels (when side-by-side) */}
      {isWideEnough && (
        <div className="cex-action-row">
          <span className="cex-action-chip">{formatActionLabel(label)}</span>
        </div>
      )}

      {/* Side-by-side or stacked state panels */}
      <div className={`cex-states-container ${!isWideEnough ? 'cex-states-stacked' : ''}`}>
        <StatePanel
          title="Pre-State"
          fields={filteredPreState}
          statusIndicator={<span className="cex-status-valid">✓ Satisfies all invariants </span>}
        />
        {/* Narrow view: centered action chip between stacked panels */}
        {!isWideEnough && filteredPostState && (
          <div className="cex-narrow-action">
            <span className="cex-action-chip">{formatActionLabel(label)}</span>
          </div>
        )}
        {filteredPostState && (
          <StatePanel
            title="Post-State"
            fields={filteredPostState}
            changes={filteredChanges}
            statusIndicator={<span className="cex-status-invalid">✗ Violates <span className="cex-property-name">{property}</span></span>}
          />
        )}
      </div>

      {/* Extra Values (collapsible, collapsed by default, shown below states) */}
      {Object.keys(remainingExtraVals).length > 0 && (
        <CollapsibleFieldsPanel title="Extra Values" fields={remainingExtraVals} />
      )}

      {/* Filter panel modal */}
      {showFilterPanel && (
        <>
          <div className="cex-filter-backdrop" onClick={() => setShowFilterPanel(false)} />
          <div className="cex-filter-panel">
            <div className="cex-filter-header">
              <span>Visible Fields</span>
              <div className="cex-filter-actions">
                <button className="cex-filter-action" onClick={showAllFields}>Show all</button>
                <button className="cex-filter-action" onClick={hideAllFields}>Hide all</button>
                <button className="cex-filter-close" onClick={() => setShowFilterPanel(false)} title="Close (Esc)">×</button>
              </div>
            </div>
            <div className="cex-filter-list">
              {allFieldNames.map(name => (
                <label key={name} className="cex-filter-item">
                  <input
                    type="checkbox"
                    checked={!hiddenFields.has(name)}
                    onChange={() => toggleFieldVisibility(name)}
                  />
                  <span>{name}</span>
                </label>
              ))}
            </div>
          </div>
        </>
      )}
    </div>
  );
};

// ========== Theorem Insertion ==========

/** Hook to create a theorem inserter function */
const useTheoremInserter = (documentUri: string, insertPosition: InsertPosition) => {
  const editorCtx = React.useContext(EditorContext);

  const insertTheorem = React.useCallback(async (theoremText: string) => {
    if (!editorCtx) {
      console.error('EditorContext not available');
      return false;
    }
    try {
      const edit = {
        textDocument: { uri: documentUri, version: null },
        edits: [{
          range: {
            start: { line: insertPosition.line, character: insertPosition.character },
            end: { line: insertPosition.line, character: insertPosition.character }
          },
          newText: '\n\n' + theoremText
        }]
      };
      await editorCtx.api.applyEdit({ documentChanges: [edit] });
      return true;
    } catch (e) {
      console.error('Failed to insert theorem:', e);
      return false;
    }
  }, [editorCtx, documentUri, insertPosition]);

  return insertTheorem;
};

/** Banner shown when there are VCs that need manual proof (unknown/error status) */
const ManualProofBanner: React.FC<{
  vcs: VerificationCondition[];
  documentUri: string;
  insertPosition: InsertPosition;
}> = ({ vcs, documentUri, insertPosition }) => {
  const insertTheorem = useTheoremInserter(documentUri, insertPosition);
  const [inserting, setInserting] = React.useState(false);
  const [dismissed, setDismissed] = React.useState(false);

  // Get VCs that need manual proof (unknown/error, not disproven - those have counterexamples)
  const needsManualProofVCs = vcs.filter(vc =>
    vc.theoremText &&
    (vc.status === 'unknown' || vc.status === 'error')
  );

  const count = needsManualProofVCs.length;
  if (count === 0 || dismissed) return null;

  const handleInsertAll = async () => {
    setInserting(true);
    const allTheorems = needsManualProofVCs
      .map(vc => vc.theoremText)
      .filter((t): t is string => t != null)
      .join('\n\n');
    await insertTheorem(allTheorems);
    setInserting(false);
  };

  return (
    <div className="vr-failure-banner">
      <span className="vr-failure-banner-icon">⚠️</span>
      <span className="vr-failure-banner-text">
        {count} verification condition{count !== 1 ? 's' : ''} could not be discharged automatically
      </span>
      <button
        className="vr-failure-banner-action"
        onClick={handleInsertAll}
        disabled={inserting}
      >
        {inserting ? 'Inserting...' : 'Insert to prove interactively'}
      </button>
      <button
        className="vr-failure-banner-dismiss"
        onClick={() => setDismissed(true)}
        title="Dismiss"
      >
        ×
      </button>
    </div>
  );
};

function getStatusIcon(status: VerificationCondition['status']): React.ReactNode {
  switch (status) {
    case 'proven': return '✅';
    case 'disproven': return '❌';
    case 'unknown': return '❓';
    case 'error': return '💥';
    case null: return <span className="spinner">⏳</span>;
    default: return '⭕';
  }
}

function getStatusClass(status: VerificationCondition['status']): string {
  return status || 'pending';
}

// Extract exceptions from dischargers (deduplicated)
function getExceptionsFromVC(vc: VerificationCondition): string[] {
  const exceptionsSet = new Set<string>();
  for (const discharger of vc.timing.dischargers) {
    // Check if status is an object with finished.res.exceptions
    if (typeof discharger.status === 'object' && discharger.status !== null) {
      const finished = (discharger.status as DischargerStatusFinished).finished;
      if (finished?.res?.exceptions) {
        for (const ex of finished.res.exceptions) {
          exceptionsSet.add(ex);
        }
      }
    }
    // Also check the result field for exceptions
    if (discharger.result?.exceptions) {
      for (const ex of discharger.result.exceptions) {
        exceptionsSet.add(ex);
      }
    }
  }
  return Array.from(exceptionsSet);
}

// Helper to check if a VC is an induction VC
function isInductionVC(vc: VerificationCondition): boolean {
  return vc.metadata.type === 'induction';
}

// Helper to get induction metadata data (returns null for trace VCs)
function getInductionData(vc: VerificationCondition): InductionMetadataData | null {
  if (vc.metadata.type === 'induction') {
    return vc.metadata.data as InductionMetadataData;
  }
  return null;
}

// Group VCs by action (only for induction VCs)
function groupByAction(vcs: VerificationCondition[]): Map<string, VerificationCondition[]> {
  const groups = new Map<string, VerificationCondition[]>();
  for (const vc of vcs) {
    const inductionData = getInductionData(vc);
    if (!inductionData) continue; // Skip non-induction VCs
    const action = inductionData.action;
    if (!groups.has(action)) {
      groups.set(action, []);
    }
    groups.get(action)!.push(vc);
  }
  return groups;
}

// Build a map from primary VC ID to its alternative VC
function buildAlternativeMap(vcs: VerificationCondition[]): Map<number, VerificationCondition> {
  const map = new Map<number, VerificationCondition>();
  for (const vc of vcs) {
    if (vc.alternativeFor != null) {
      map.set(vc.alternativeFor, vc);
    }
  }
  return map;
}

// Filter to only show primary induction VCs (exclude all alternatives, trace VCs, and dormant VCs)
function filterToVisibleVCs(vcs: VerificationCondition[]): VerificationCondition[] {
  return vcs.filter(vc => vc.alternativeFor == null && isInductionVC(vc) && !vc.isDormant);
}

// ========== Components ==========

function getFilterButtonContent(filter: StatusFilter): React.ReactNode {
  const label = filter === 'all' ? 'All' : filter.charAt(0).toUpperCase() + filter.slice(1);

  switch (filter) {
    case 'all':
      return label;
    case 'pending':
      return <><span className="spinner-small">⏳</span> {label}</>;
    case 'proven':
      return <>✅ {label}</>;
    case 'disproven':
      return <>❌ {label}</>;
    case 'unknown':
      return <>❓ {label}</>;
    case 'error':
      return <>💥 {label}</>;
    default:
      return label;
  }
}

interface PropertyRowProps {
  vc: VerificationCondition;
  alternativeVC?: VerificationCondition;
  documentUri: string;
  insertPosition: InsertPosition;
  serverTime: number;
}

const PropertyRow: React.FC<PropertyRowProps> = ({ vc, alternativeVC, documentUri, insertPosition, serverTime }) => {
  const [expanded, setExpanded] = React.useState(false);
  const [showTRCounterexample, setShowTRCounterexample] = React.useState(true);
  const [showRawHtml, setShowRawHtml] = React.useState(false);

  // Cache the last known time to prevent flickering during state transitions
  const lastKnownTimeRef = React.useRef<number | null>(null);

  // Theorem insertion
  const insertTheorem = useTheoremInserter(documentUri, insertPosition);
  // Only highlight unknown/error as "needs manual proof" - disproven VCs have counterexamples and aren't provable
  const needsManualProof = vc.status === 'unknown' || vc.status === 'error';
  const hasTheoremText = !!vc.theoremText;
  const hasTRTheoremText = !!alternativeVC?.theoremText;

  const formatTime = (ms: number | null) => {
    if (ms === null) return null;
    if (ms < 1000) return `${ms}ms`;
    return `${(ms / 1000).toFixed(2)}s`;
  };

  // Check if the alternative (TR) VC is running (not dormant, but no result yet)
  const trIsRunning = alternativeVC && !alternativeVC.isDormant && alternativeVC.status === null;

  // Check if the alternative (TR) VC completed (not dormant and has a result)
  const trCompleted = alternativeVC && !alternativeVC.isDormant && alternativeVC.status !== null;

  // TR was invoked means it's either running or completed
  const trWasInvoked = trIsRunning || trCompleted;

  // Get counterexample from a VC
  const getFirstCounterexample = (targetVC: VerificationCondition): Counterexample | null => {
    if (targetVC.status !== 'disproven') return null;

    for (const discharger of targetVC.timing.dischargers) {
      const counterexamples = discharger.result?.data?.counterexamples;
      if (counterexamples && counterexamples.length > 0) {
        return counterexamples[0];
      }
    }
    return null;
  };

  const wpCounterexample = getFirstCounterexample(vc);
  const trCounterexample = alternativeVC ? getFirstCounterexample(alternativeVC) : null;

  // Determine which counterexample to show (prefer TR when available)
  const hasWPCounterexample = wpCounterexample !== null;
  const hasTRCounterexample = trCounterexample !== null;
  const hasAnyCounterexample = hasWPCounterexample || hasTRCounterexample;
  const hasBothCounterexamples = hasWPCounterexample && hasTRCounterexample;

  // Default to TR counterexample if available, otherwise WP
  const activeCounterexample = (showTRCounterexample && trCounterexample) || wpCounterexample;

  // Get all exceptions from both VCs (deduplicated)
  const allExceptions = React.useMemo(() => {
    const set = new Set<string>();
    for (const ex of getExceptionsFromVC(vc)) set.add(ex);
    if (alternativeVC) {
      for (const ex of getExceptionsFromVC(alternativeVC)) set.add(ex);
    }
    return Array.from(set);
  }, [vc, alternativeVC]);
  const hasExceptions = allExceptions.length > 0;

  // Row is expandable if it has counterexamples or exceptions
  const isExpandable = hasAnyCounterexample || hasExceptions;

  // Helper to check if any discharger is currently running
  const isAnyDischargerRunning = (targetVC: VerificationCondition): boolean => {
    return targetVC.timing.dischargers.some(d => d.status === 'running');
  };

  // Helper to compute elapsed time for a running VC
  const getRunningElapsedTime = (targetVC: VerificationCondition): number | null => {
    const runningDischarger = targetVC.timing.dischargers.find(
      d => d.status === 'running' && d.startTime !== null
    );
    if (runningDischarger?.startTime != null) {
      return serverTime - runningDischarger.startTime;
    }
    return null;
  };

  // Check if this VC is queued (pending but no dischargers running yet)
  const isQueued = vc.status === null && !isAnyDischargerRunning(vc);

  // Format elapsed time with in-progress styling (reduced opacity)
  const formatElapsedTime = (elapsed: number | null): React.ReactNode => {
    if (elapsed !== null) {
      return <span className="time-in-progress">{formatTime(elapsed)}</span>;
    }
    return null;
  };

  // Get elapsed time from any discharger with a startTime (regardless of status)
  const getElapsedTimeFromAnyDischarger = (targetVC: VerificationCondition): number | null => {
    const dischargerWithStartTime = targetVC.timing.dischargers.find(d => d.startTime !== null);
    if (dischargerWithStartTime?.startTime != null) {
      return serverTime - dischargerWithStartTime.startTime;
    }
    return null;
  };

  // Get the best available time for a VC, trying multiple sources
  const getVCTime = (targetVC: VerificationCondition): number | null => {
    // First try totalTime
    if (targetVC.timing.totalTime !== null) {
      return targetVC.timing.totalTime;
    }
    // Try successfulDischargerTime
    if (targetVC.timing.successfulDischargerTime !== undefined) {
      return targetVC.timing.successfulDischargerTime;
    }
    // Try to get time from finished dischargers
    const finishedDischarger = targetVC.timing.dischargers.find(d => d.time !== null);
    if (finishedDischarger && finishedDischarger.time !== null) {
      return finishedDischarger.time;
    }
    // Fall back to elapsed time from any discharger with startTime (covers transition period)
    return getElapsedTimeFromAnyDischarger(targetVC);
  };

  // Format the time display
  const getTimeDisplay = (): React.ReactNode => {
    // Helper to get time with caching - once we have a time, we keep it
    const getTimeWithCache = (): number | null => {
      let currentTime: number | null = null;

      if (vc.status === null) {
        // VC is running - get elapsed time
        currentTime = getRunningElapsedTime(vc);
      } else {
        // VC has finished - get the best available time
        currentTime = getVCTime(vc);
      }

      // Update cache if we have a valid time
      if (currentTime !== null) {
        lastKnownTimeRef.current = currentTime;
      }

      // Return current time, or fall back to cached time
      return currentTime ?? lastKnownTimeRef.current;
    };

    const primaryTime = getTimeWithCache();

    // If primary VC is still running, show elapsed time with in-progress styling
    if (vc.status === null) {
      return formatElapsedTime(primaryTime);
    }

    // VC has finished
    const wpTime = formatTime(primaryTime);

    if (trIsRunning) {
      // TR is running: show WP time + elapsed TR time
      const trElapsed = getRunningElapsedTime(alternativeVC!);
      const trTimeDisplay = formatElapsedTime(trElapsed);
      return wpTime && trTimeDisplay
        ? <>{wpTime}+{trTimeDisplay}</>
        : trTimeDisplay || wpTime;
    }

    if (trCompleted) {
      // TR completed: show combined timing
      const trTime = formatTime(getVCTime(alternativeVC));
      if (wpTime && trTime) {
        return `${wpTime}+${trTime}`;
      }
      return trTime || wpTime;
    }

    return wpTime;
  };

  const timeDisplay = getTimeDisplay();

  // Handle click on property row
  const handleRowClick = async (e: React.MouseEvent) => {
    const isCmdOrCtrl = e.metaKey || e.ctrlKey;

    // Cmd+Shift+click to insert TR version
    if (isCmdOrCtrl && e.shiftKey && hasTRTheoremText) {
      e.preventDefault();
      e.stopPropagation();
      await insertTheorem(alternativeVC!.theoremText!);
      return;
    }

    // Cmd-click (Mac) or Ctrl-click (Windows/Linux) to insert theorem
    if (isCmdOrCtrl && hasTheoremText) {
      e.preventDefault();
      e.stopPropagation();
      await insertTheorem(vc.theoremText!);
      return;
    }

    // Normal click: toggle expanded
    if (isExpandable) {
      setExpanded(!expanded);
    }
  };

  // Build tooltip text based on available actions
  const getTooltip = (): string | undefined => {
    const parts: string[] = [];
    if (hasTheoremText) parts.push('Cmd-click to insert theorem');
    if (hasTRTheoremText) parts.push('Cmd+Shift-click for TR version');
    return parts.length > 0 ? parts.join(', ') : undefined;
  };

  return (
    <>
      <div
        className={`property-row status-${getStatusClass(vc.status)} ${isExpandable ? 'expandable' : ''} ${needsManualProof && hasTheoremText ? 'insertable' : ''}`}
        onClick={handleRowClick}
        style={{ cursor: isExpandable || hasTheoremText ? 'pointer' : 'default' }}
        title={getTooltip()}
      >
        {isExpandable && (
          <span className="property-toggle">{expanded ? '▼' : '▶'}</span>
        )}
        <span className="property-icon">{isQueued ? '⏳' : getStatusIcon(vc.status)}</span>
        <span className="property-name">{getInductionData(vc)?.property}</span>
        {trWasInvoked && (
          <span className={`vc-style-badge tr-badge ${trIsRunning ? 'tr-running' : ''}`}>
            TR{trIsRunning && '...'}
          </span>
        )}
        {timeDisplay && (
          <span className="property-time">{timeDisplay}</span>
        )}
      </div>
      {expanded && hasExceptions && (
        <div className="exceptions-container">
          <div className="exceptions-label">Exceptions</div>
          <div className="exceptions-content">
            {allExceptions.map((exception, idx) => (
              <pre key={idx} className="exception-item">{exception}</pre>
            ))}
          </div>
        </div>
      )}
      {expanded && activeCounterexample && (
        <div className="counterexample-container">
          {activeCounterexample.structuredJson && !showRawHtml ? (
            <StructuredCexView
              data={activeCounterexample.structuredJson}
              property={getInductionData(vc)?.property ?? ''}
              headerRightContent={
                <>
                  <button
                    className="cex-view-toggle"
                    onClick={(e) => { e.stopPropagation(); setShowRawHtml(!showRawHtml); }}
                  >
                    Show raw model
                  </button>
                  {hasBothCounterexamples && (
                    <div className="counterexample-toggle">
                      <button
                        className={`cex-toggle-btn ${showTRCounterexample ? 'active' : ''}`}
                        onClick={(e) => { e.stopPropagation(); setShowTRCounterexample(true); }}
                      >
                        TR
                      </button>
                      <button
                        className={`cex-toggle-btn ${!showTRCounterexample ? 'active' : ''}`}
                        onClick={(e) => { e.stopPropagation(); setShowTRCounterexample(false); }}
                      >
                        WP
                      </button>
                    </div>
                  )}
                </>
              }
            />
          ) : (
            <>
              <div className="counterexample-header">
                <div className="counterexample-label">Counterexample</div>
                <div className="counterexample-toggles">
                  {activeCounterexample.structuredJson && (
                    <button
                      className="cex-view-toggle"
                      onClick={(e) => { e.stopPropagation(); setShowRawHtml(!showRawHtml); }}
                    >
                      Show structured
                    </button>
                  )}
                  {hasBothCounterexamples && (
                    <div className="counterexample-toggle">
                      <button
                        className={`cex-toggle-btn ${showTRCounterexample ? 'active' : ''}`}
                        onClick={(e) => { e.stopPropagation(); setShowTRCounterexample(true); }}
                      >
                        TR
                      </button>
                      <button
                        className={`cex-toggle-btn ${!showTRCounterexample ? 'active' : ''}`}
                        onClick={(e) => { e.stopPropagation(); setShowTRCounterexample(false); }}
                      >
                        WP
                      </button>
                    </div>
                  )}
                </div>
              </div>
              <div className="counterexample-content">
                {typeof activeCounterexample.html === 'string'
                  ? <span dangerouslySetInnerHTML={{ __html: activeCounterexample.html }} />
                  : <HtmlDisplay html={activeCounterexample.html} />
                }
              </div>
            </>
          )}
        </div>
      )}
    </>
  );
};

interface ActionSectionProps {
  action: string;
  vcs: VerificationCondition[];
  alternativeMap: Map<number, VerificationCondition>;
  documentUri: string;
  insertPosition: InsertPosition;
  serverTime: number;
}

const ActionSection: React.FC<ActionSectionProps> = ({ action, vcs, alternativeMap, documentUri, insertPosition, serverTime }) => {
  const [expanded, setExpanded] = React.useState(true);
  const insertTheorem = useTheoremInserter(documentUri, insertPosition);
  const [inserting, setInserting] = React.useState(false);

  // Get VCs that need manual proof (unknown/error, not disproven - those have counterexamples)
  const needsManualProofVCs = vcs.filter(vc =>
    vc.theoremText &&
    (vc.status === 'unknown' || vc.status === 'error')
  );
  const needsManualProofCount = needsManualProofVCs.length;

  const handleInsertNeedsProof = async (e: React.MouseEvent) => {
    e.stopPropagation();
    if (needsManualProofCount === 0) return;
    setInserting(true);
    const allTheorems = needsManualProofVCs
      .map(vc => vc.theoremText)
      .filter((t): t is string => t != null)
      .join('\n\n');
    await insertTheorem(allTheorems);
    setInserting(false);
  };

  return (
    <div className="action-section">
      <div className="action-header" onClick={() => setExpanded(!expanded)}>
        <span className="action-toggle">{expanded ? '▼' : '▶'}</span>
        <span className="action-name">{action}</span>
        {needsManualProofCount > 0 && (
          <>
            <span className="action-failed-count">({needsManualProofCount} need{needsManualProofCount === 1 ? 's' : ''} manual proof)</span>
            <button
              className="action-insert-failed"
              onClick={handleInsertNeedsProof}
              disabled={inserting}
            >
              {inserting ? 'Inserting...' : 'Insert'}
            </button>
          </>
        )}
      </div>
      {expanded && (
        <div className="action-properties">
          {vcs.map((vc) => (
            <PropertyRow
              key={vc.id}
              vc={vc}
              documentUri={documentUri}
              insertPosition={insertPosition}
              alternativeVC={alternativeMap.get(vc.id)}
              serverTime={serverTime}
            />
          ))}
        </div>
      )}
    </div>
  );
};

const VerificationResultsView: React.FC<VerificationResultsProps> = ({ results, insertPosition, documentUri }) => {
  const [statusFilter, setStatusFilter] = React.useState<StatusFilter>('all');
  const [showRawJson, setShowRawJson] = React.useState(false);

  // Compute status colors with consistent semantic colors across all themes
  const statusColors = React.useMemo(() => {
    const withOpacity = (color: string, opacity: number): string => {
      // Parse hex color to rgba
      const hex = color.replace('#', '');
      const r = parseInt(hex.substring(0, 2), 16);
      const g = parseInt(hex.substring(2, 4), 16);
      const b = parseInt(hex.substring(4, 6), 16);
      return `rgba(${r}, ${g}, ${b}, ${opacity})`;
    }

    // Use consistent semantic colors across all themes
    return {
      proven: {
        border: '#52c41a',  // green
        bg: withOpacity('#52c41a', 0.1),
      },
      disproven: {
        border: '#ff4d4f',  // red
        bg: withOpacity('#ff4d4f', 0.1),
      },
      error: {
        border: '#fa8c16',  // orange
        bg: withOpacity('#fa8c16', 0.1),
      },
      unknown: {
        border: '#1890ff',  // blue
        bg: withOpacity('#1890ff', 0.1),
      },
      pending: {
        border: '#d9d9d9',  // gray
        bg: withOpacity('#d9d9d9', 0.05),
      },
    }
  }, []);

  // Build map from primary VC ID to its alternative VC (from ALL VCs including dormant)
  const alternativeMap = React.useMemo(
    () => buildAlternativeMap(results.vcs),
    [results.vcs]
  );

  // Filter to only show primary VCs (alternatives are shown inline with their primary)
  const visibleVCs = React.useMemo(
    () => filterToVisibleVCs(results.vcs),
    [results.vcs]
  );

  // Compute counts for each status (only from visible/non-dormant VCs)
  const statusCounts = React.useMemo(() => {
    const counts = {
      all: visibleVCs.length,
      pending: 0,
      proven: 0,
      disproven: 0,
      unknown: 0,
      error: 0,
    };

    visibleVCs.forEach((vc) => {
      if (vc.status === null) {
        counts.pending++;
      } else if (vc.status === 'proven') {
        counts.proven++;
      } else if (vc.status === 'disproven') {
        counts.disproven++;
      } else if (vc.status === 'unknown') {
        counts.unknown++;
      } else if (vc.status === 'error') {
        counts.error++;
      }
    });

    return counts;
  }, [visibleVCs]);

  // Filter VCs based on status (from already-visible VCs)
  const filteredVCs = React.useMemo(() => {
    if (statusFilter === 'all') return visibleVCs;
    if (statusFilter === 'pending') return visibleVCs.filter((vc) => vc.status === null);
    return visibleVCs.filter((vc) => vc.status === statusFilter);
  }, [visibleVCs, statusFilter]);

  // Group VCs by action
  const actionGroups = React.useMemo(() => groupByAction(filteredVCs), [filteredVCs]);

  // Separate initialization from other actions
  const initializationVCs = actionGroups.get('initializer') || [];
  const otherActions = Array.from(actionGroups.entries()).filter(
    ([action]) => action !== 'initializer'
  );

  const styles = React.useMemo(() => `
    .vr-root {
      font-family: system-ui, -apple-system, sans-serif;
      max-width: 100%;
      padding: 16px;
      background: var(--vscode-editor-background);
      border-radius: 8px;
    }

    .vr-filters {
      display: flex;
      gap: 8px;
      margin-bottom: 16px;
      padding: 12px;
      background: var(--vscode-editorWidget-background);
      border: 1px solid var(--vscode-panel-border);
      border-radius: 6px;
      flex-wrap: wrap;
      align-items: center;
    }

    .vr-filter-label {
      font-weight: 600;
      font-size: 14px;
      color: var(--vscode-foreground);
    }

    .vr-filter-button {
      padding: 6px 12px;
      border: 1px solid var(--vscode-panel-border);
      background: var(--vscode-editorWidget-background);
      color: var(--vscode-foreground);
      border-radius: 4px;
      cursor: pointer;
      font-size: 13px;
      transition: all 0.2s;
    }

    .vr-filter-button:hover {
      background: var(--vscode-list-hoverBackground);
      border-color: var(--vscode-panel-border);
    }

    .vr-filter-button.active {
      background: var(--vscode-button-background);
      color: var(--vscode-button-foreground);
      border-color: var(--vscode-button-background);
    }

    .vr-section {
      margin-bottom: 24px;
      background: var(--vscode-editorWidget-background);
      border: 1px solid var(--vscode-panel-border);
      border-radius: 6px;
      overflow: hidden;
    }

    .vr-section-title {
      font-weight: 600;
      font-size: 16px;
      padding: 12px 16px;
      background: var(--vscode-editorGroupHeader-tabsBackground);
      border-bottom: 1px solid var(--vscode-panel-border);
      color: var(--vscode-foreground);
    }

    .vr-section-content {
      padding: 12px;
    }

    .action-section {
      margin-bottom: 12px;
      border: 1px solid var(--vscode-panel-border);
      border-radius: 4px;
      overflow: hidden;
    }

    .action-header {
      display: flex;
      align-items: center;
      gap: 8px;
      padding: 10px 12px;
      background: var(--vscode-editorWidget-background);
      cursor: pointer;
      user-select: none;
      transition: background 0.2s;
    }

    .action-header:hover {
      background: var(--vscode-list-hoverBackground);
    }

    .action-toggle {
      font-size: 12px;
      color: var(--vscode-descriptionForeground);
    }

    .action-name {
      font-weight: 600;
      font-size: 14px;
      color: var(--vscode-foreground);
    }

    .action-properties {
      padding: 8px 12px 8px 32px;
      background: var(--vscode-editorWidget-background);
    }

    .property-row {
      display: flex;
      align-items: center;
      gap: 8px;
      padding: 6px 8px;
      margin: 2px 0;
      border-radius: 4px;
      transition: background 0.15s;
    }

    .property-row:hover {
      background: var(--vscode-list-hoverBackground);
    }

    .property-icon {
      font-size: 16px;
      flex-shrink: 0;
    }

    .property-name {
      font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
      font-size: 13px;
      color: var(--vscode-editor-foreground);
      flex-grow: 1;
    }

    .property-time {
      font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
      font-size: 12px;
      margin-left: auto;
      padding: 2px 6px;
      background: var(--vscode-editorWidget-background);
      color: var(--vscode-descriptionForeground);
      border: 1px solid var(--vscode-panel-border);
      border-radius: 6px;
      white-space: nowrap;
    }

    .time-in-progress {
      opacity: 0.6;
    }

    /* Failure banner */
    .vr-failure-banner {
      display: flex;
      align-items: center;
      gap: 10px;
      padding: 10px 14px;
      margin-bottom: 16px;
      background: rgba(255, 77, 79, 0.08);
      border: 1px solid rgba(255, 77, 79, 0.3);
      border-radius: 6px;
    }

    .vr-failure-banner-icon {
      font-size: 16px;
      flex-shrink: 0;
    }

    .vr-failure-banner-text {
      font-size: 13px;
      color: var(--vscode-foreground);
      flex-grow: 1;
    }

    .vr-failure-banner-action {
      padding: 5px 12px;
      background: var(--vscode-button-secondaryBackground);
      color: var(--vscode-button-secondaryForeground);
      border: 1px solid var(--vscode-panel-border);
      border-radius: 4px;
      cursor: pointer;
      font-size: 12px;
      white-space: nowrap;
      transition: all 0.15s;
    }

    .vr-failure-banner-action:hover {
      background: var(--vscode-button-secondaryHoverBackground);
    }

    .vr-failure-banner-action:disabled {
      opacity: 0.5;
      cursor: not-allowed;
    }

    .vr-failure-banner-dismiss {
      padding: 2px 8px;
      background: transparent;
      border: none;
      color: var(--vscode-descriptionForeground);
      cursor: pointer;
      font-size: 16px;
      line-height: 1;
      border-radius: 3px;
      transition: all 0.15s;
    }

    .vr-failure-banner-dismiss:hover {
      background: var(--vscode-toolbar-hoverBackground);
      color: var(--vscode-foreground);
    }

    /* Section-level failed count and insert action */
    .action-failed-count {
      font-size: 12px;
      color: #ff4d4f;
      margin-left: 8px;
    }

    .action-insert-failed {
      margin-left: auto;
      padding: 3px 10px;
      background: transparent;
      color: var(--vscode-textLink-foreground);
      border: none;
      cursor: pointer;
      font-size: 12px;
      border-radius: 3px;
      transition: all 0.15s;
    }

    .action-insert-failed:hover {
      background: var(--vscode-toolbar-hoverBackground);
      text-decoration: underline;
    }

    .action-insert-failed:disabled {
      opacity: 0.5;
      cursor: not-allowed;
    }

    /* Visual hint for cmd-clickable property names */
    .property-row.insertable .property-name {
      text-decoration: underline dotted;
      text-underline-offset: 2px;
    }

    .property-row.status-proven {
      background: ${statusColors.proven.bg};
      border-left: 3px solid ${statusColors.proven.border};
    }

    .property-row.status-disproven {
      background: ${statusColors.disproven.bg};
      border-left: 3px solid ${statusColors.disproven.border};
    }

    .property-row.status-error {
      background: ${statusColors.error.bg};
      border-left: 3px solid ${statusColors.error.border};
    }

    .property-row.status-unknown {
      background: ${statusColors.unknown.bg};
      border-left: 3px solid ${statusColors.unknown.border};
    }

    .property-row.status-pending {
      background: ${statusColors.pending.bg};
      border-left: 3px solid ${statusColors.pending.border};
    }

    .spinner {
      display: inline-block;
      animation: spin 2s linear infinite;
    }

    .spinner-small {
      display: inline-block;
      font-size: 14px;
    }

    @keyframes spin {
      0% { transform: rotate(0deg); }
      100% { transform: rotate(360deg); }
    }

    .vr-empty {
      padding: 24px;
      text-align: center;
      color: var(--vscode-disabledForeground);
      font-style: italic;
    }

    .property-row.expandable:hover {
      background: var(--vscode-list-activeSelectionBackground);
      opacity: 0.9;
    }

    .property-toggle {
      font-size: 12px;
      color: var(--vscode-descriptionForeground);
      margin-right: 4px;
      flex-shrink: 0;
    }

    .counterexample-container {
      margin-left: 32px;
      margin-top: 8px;
      margin-bottom: 8px;
      padding: 12px;
      background: var(--vscode-editorWidget-background);
      border-left: 3px solid #ff4d4f;
      border-radius: 4px;
      overflow-x: auto;
    }

    .counterexample-label {
      font-weight: 600;
      font-size: 12px;
      color: var(--vscode-descriptionForeground);
      margin-bottom: 8px;
      text-transform: uppercase;
      letter-spacing: 0.5px;
    }

    .counterexample-content {
      font-size: 13px;
      color: var(--vscode-editor-foreground);
    }

    .exceptions-container {
      margin-left: 32px;
      margin-top: 8px;
      margin-bottom: 8px;
      padding: 12px;
      background: var(--vscode-editorWidget-background);
      border-left: 3px solid #fa8c16;
      border-radius: 4px;
      overflow-x: auto;
    }

    .exceptions-label {
      font-weight: 600;
      font-size: 12px;
      color: var(--vscode-descriptionForeground);
      margin-bottom: 8px;
      text-transform: uppercase;
      letter-spacing: 0.5px;
    }

    .exceptions-content {
      display: flex;
      flex-direction: column;
      gap: 8px;
    }

    .exception-item {
      margin: 0;
      padding: 8px 12px;
      background: var(--vscode-inputValidation-errorBackground, rgba(250, 140, 22, 0.1));
      border: 1px solid var(--vscode-inputValidation-errorBorder, #fa8c16);
      border-radius: 4px;
      font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, "Liberation Mono", monospace;
      font-size: 12px;
      color: var(--vscode-editor-foreground);
      white-space: pre-wrap;
      word-break: break-word;
      overflow-wrap: break-word;
    }

    .counterexample-column-header {
      text-align: left;
    }

    .counterexample-header {
      display: flex;
      justify-content: space-between;
      align-items: center;
      margin-bottom: 8px;
    }

    .counterexample-toggle {
      display: flex;
      gap: 4px;
    }

    .cex-toggle-btn {
      padding: 2px 8px;
      font-size: 11px;
      font-weight: 500;
      border: 1px solid var(--vscode-panel-border);
      background: var(--vscode-editorWidget-background);
      color: var(--vscode-foreground);
      border-radius: 3px;
      cursor: pointer;
      transition: all 0.15s;
    }

    .cex-toggle-btn:hover {
      background: var(--vscode-list-hoverBackground);
    }

    .cex-toggle-btn.active {
      background: var(--vscode-button-background);
      color: var(--vscode-button-foreground);
      border-color: var(--vscode-button-background);
    }

    .vc-style-badge {
      font-size: 10px;
      font-weight: 600;
      padding: 2px 6px;
      border-radius: 3px;
      text-transform: uppercase;
      letter-spacing: 0.5px;
      flex-shrink: 0;
    }

    .tr-badge {
      background: rgba(24, 144, 255, 0.15);
      color: #1890ff;
      border: 1px solid rgba(24, 144, 255, 0.3);
    }

    .tr-badge.tr-running {
      animation: pulse 1.5s ease-in-out infinite;
    }

    @keyframes pulse {
      0%, 100% {
        opacity: 1;
        background: rgba(24, 144, 255, 0.15);
      }
      50% {
        opacity: 0.7;
        background: rgba(24, 144, 255, 0.3);
      }
    }

    .vr-toolbar {
      display: flex;
      justify-content: flex-end;
      padding: 4px 0;
      margin-bottom: 8px;
    }

    ${generateToggleLinkCSS('vr')}
    ${generateJsonViewCSS('vr')}

    /* Structured counterexample styles */
    .counterexample-toggles {
      display: flex;
      gap: 12px;
      align-items: center;
    }

    .cex-view-toggle {
      font-size: 11px;
      color: var(--vscode-textLink-foreground);
      cursor: pointer;
      text-decoration: none;
      background: none;
      border: none;
      padding: 2px 6px;
      border-radius: 3px;
    }

    .cex-view-toggle:hover {
      text-decoration: underline;
      background: var(--vscode-toolbar-hoverBackground);
    }

    .cex-structured-view {
      font-family: system-ui, -apple-system, sans-serif;
    }

    .cex-header-row {
      display: flex;
      justify-content: space-between;
      align-items: center;
      margin-bottom: 12px;
    }

    .cex-header-left {
      display: flex;
      align-items: center;
      gap: 12px;
    }

    .cex-header-right {
      display: flex;
      align-items: center;
      gap: 12px;
    }

    .cex-header-label {
      font-weight: 600;
      font-size: 12px;
      color: var(--vscode-descriptionForeground);
      text-transform: uppercase;
      letter-spacing: 0.5px;
    }

    ${generateInstantiationCSS('cex')}

    .cex-action-chip {
      display: inline-block;
      font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
      font-size: 12px;
      font-weight: 600;
      background: var(--vscode-activityBarBadge-background, #007acc);
      color: var(--vscode-activityBarBadge-foreground, #fff);
      border-radius: 999px;
      padding: 4px 12px;
      line-height: 1.4;
    }

    .cex-states-container {
      display: flex;
      gap: 16px;
      flex-wrap: wrap;
    }

    .cex-states-container.cex-states-stacked {
      flex-direction: column;
    }

    .cex-narrow-action {
      display: flex;
      justify-content: center;
      align-items: center;
      padding: 8px 0;
      width: 100%;
    }

    .cex-action-row {
      display: flex;
      justify-content: center;
      align-items: center;
      padding: 12px 0;
      margin-bottom: 12px;
    }

    .cex-state-panel {
      flex: 1;
      min-width: 280px;
      max-width: 100%;
      background: var(--vscode-editor-background);
      border: 1px solid var(--vscode-panel-border);
      border-radius: 6px;
      overflow: hidden;
    }

    .cex-state-header {
      display: flex;
      justify-content: space-between;
      align-items: center;
      font-weight: 600;
      font-size: 12px;
      padding: 8px 12px;
      background: var(--vscode-editorGroupHeader-tabsBackground);
      border-bottom: 1px solid var(--vscode-panel-border);
      color: var(--vscode-foreground);
      text-transform: uppercase;
      letter-spacing: 0.5px;
    }

    .cex-state-status {
      font-size: 10px;
      font-weight: 500;
      text-transform: none;
      letter-spacing: normal;
    }

    .cex-status-valid {
      color: var(--vscode-testing-iconPassed, #4caf50);
    }

    .cex-status-invalid {
      color: var(--vscode-testing-iconFailed, #f44336);
    }

    .cex-property-name {
      font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
      font-weight: 600;
    }

    .cex-state-body {
      padding: 8px;
    }

    .cex-empty-state {
      padding: 12px;
      text-align: center;
      color: var(--vscode-disabledForeground);
      font-style: italic;
      font-size: 12px;
    }

    .cex-kv-table {
      border: 1px solid var(--vscode-panel-border);
      border-radius: 4px;
      overflow: hidden;
    }

    .cex-kv-row {
      display: grid;
      grid-template-columns: minmax(80px, auto) auto 1fr;
      gap: 8px;
      padding: 6px 10px;
      align-items: baseline;
      border-bottom: 1px solid var(--vscode-panel-border);
      background: var(--vscode-editorWidget-background);
      transition: background-color 0.15s ease, border-left-color 0.15s ease;
      border-left: 3px solid transparent;
    }

    .cex-kv-row:last-child {
      border-bottom: none;
    }

    .cex-kv-row.changed {
      background: var(--vscode-editor-findMatchHighlightBackground, rgba(255, 213, 0, 0.15));
      border-left: 3px solid var(--vscode-editor-findMatchHighlightBorder, #ffd500);
    }

    .cex-kv-key {
      font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
      font-size: 11px;
      word-break: break-all;
    }

    .cex-kv-key code {
      background: transparent;
      padding: 0;
      color: var(--vscode-foreground);
    }

    .cex-kv-sep {
      color: var(--vscode-descriptionForeground);
      font-size: 11px;
    }

    .cex-kv-val {
      font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
      font-size: 11px;
      word-break: break-all;
    }

    .cex-kv-val code {
      background: transparent;
      padding: 0;
      color: var(--vscode-foreground);
    }

    ${sharedDiffCSS}
    ${sharedListCSS}

    .cex-toolbar {
      display: flex;
      gap: 12px;
    }

    .cex-toolbar-btn {
      font-size: 11px;
      color: var(--vscode-textLink-foreground);
      cursor: pointer;
      text-decoration: none;
      background: none;
      border: none;
      padding: 2px 6px;
      border-radius: 3px;
    }

    .cex-toolbar-btn:hover {
      text-decoration: underline;
      background: var(--vscode-toolbar-hoverBackground);
    }

    ${generateFilterPanelCSS('cex')}

    /* Theory panel styles (collapsible) */
    .cex-theory-panel {
      margin-bottom: 12px;
      background: var(--vscode-editor-background);
      border: 1px solid var(--vscode-panel-border);
      border-radius: 6px;
      overflow: hidden;
    }

    /* Add gap when theory panel follows states container (for Extra Values) */
    .cex-states-container + .cex-theory-panel {
      margin-top: 12px;
    }

    .cex-theory-header {
      display: flex;
      align-items: center;
      gap: 8px;
      padding: 8px 12px;
      background: var(--vscode-editorGroupHeader-tabsBackground);
      cursor: pointer;
      user-select: none;
      transition: background 0.2s;
    }

    .cex-theory-header:hover {
      background: var(--vscode-list-hoverBackground);
    }

    .cex-theory-toggle {
      font-size: 10px;
      color: var(--vscode-descriptionForeground);
    }

    .cex-theory-label {
      font-weight: 600;
      font-size: 12px;
      text-transform: uppercase;
      letter-spacing: 0.5px;
      color: var(--vscode-foreground);
    }

    .cex-theory-count {
      font-size: 11px;
      color: var(--vscode-descriptionForeground);
    }

    .cex-theory-body {
      padding: 8px;
      border-top: 1px solid var(--vscode-panel-border);
    }

  `, [statusColors]);

  const prettyJson = JSON.stringify(results, null, 2);

  return (
    <>
      <style>{styles}</style>
      <div className="vr-root">
        {/* Toolbar with JSON toggle */}
        <div className="vr-toolbar">
          <button className="vr-toggle-link" onClick={() => setShowRawJson(!showRawJson)}>
            {showRawJson ? "Show formatted" : "Show JSON"}
          </button>
        </div>

        {showRawJson ? (
          <div className="vr-json-view">
            <CopyButton text={prettyJson} className="vr-copy-button" />
            <div className="vr-json-content">
              {prettyJson}
            </div>
          </div>
        ) : (
          <>
            {/* Filters */}
            <div className="vr-filters">
              <span className="vr-filter-label">Filter by status ({visibleVCs.length} VCs):</span>
              {(['all', 'pending', 'proven', 'disproven', 'unknown', 'error'] as StatusFilter[]).map((filter) => {
                // Only show filter buttons for groups with elements
                if (statusCounts[filter] === 0) return null;
                return (
                  <button
                    key={filter}
                    className={`vr-filter-button ${statusFilter === filter ? 'active' : ''}`}
                    onClick={() => setStatusFilter(filter)}
                  >
                    {getFilterButtonContent(filter)} ({statusCounts[filter]})
                  </button>
                );
              })}
            </div>

            {/* Banner for VCs needing manual proof */}
            <ManualProofBanner
              vcs={visibleVCs}
              documentUri={documentUri}
              insertPosition={insertPosition}
            />

            {filteredVCs.length === 0 ? (
              <div className="vr-empty">No verification conditions match the selected filter.</div>
            ) : (
              <>
                {/* Initialization Section */}
                {initializationVCs.length > 0 && (
                  <div className="vr-section">
                    <div className="vr-section-title">
                      Initialization must establish the invariant:
                    </div>
                    <div className="vr-section-content">
                      <div className="action-properties">
                        {initializationVCs.map((vc) => (
                          <PropertyRow
                            key={vc.id}
                            vc={vc}
                            alternativeVC={alternativeMap.get(vc.id)}
                            documentUri={documentUri}
                            insertPosition={insertPosition}
                            serverTime={results.serverTime}
                          />
                        ))}
                      </div>
                    </div>
                  </div>
                )}

                {/* Actions Section */}
                {otherActions.length > 0 && (
                  <div className="vr-section">
                    <div className="vr-section-title">
                      The following set of actions must preserve the invariant:
                    </div>
                    <div className="vr-section-content">
                      {otherActions.map(([action, vcs]) => (
                        <ActionSection
                          key={action}
                          action={action}
                          vcs={vcs}
                          alternativeMap={alternativeMap}
                          documentUri={documentUri}
                          insertPosition={insertPosition}
                          serverTime={results.serverTime}
                        />
                      ))}
                    </div>
                  </div>
                )}
              </>
            )}
          </>
        )}
      </div>
    </>
  );
};

export default VerificationResultsView;
