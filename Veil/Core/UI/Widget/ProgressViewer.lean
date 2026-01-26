/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Pîrlea
-/
import Lean.Server.Rpc.Basic
import Lean.Elab.Command

import ProofWidgets.Component.Basic
import ProofWidgets.Component.HtmlDisplay
import Veil.Core.UI.Widget.RefreshComponent
import Veil.Core.Tools.ModelChecker.Concrete.Progress
import Veil.Core.UI.Trace.TraceDisplay
import ProofWidgets.Component.Recharts

namespace Veil.ModelChecker

open Lean Server Elab Command ProofWidgets Jsx Veil.ModelChecker.Concrete RefreshComponent Recharts

/-- Props for Recharts Tooltip (empty for default behavior). -/
structure TooltipProps where
  deriving FromJson, ToJson

/-- Tooltip component for Recharts. See https://recharts.org/en-US/api/Tooltip -/
def Tooltip : Component TooltipProps where
  javascript := Recharts.javascript
  «export» := "Tooltip"

/-- Extended axis props with label support. -/
structure LabeledAxisProps where
  dataKey? : Option Json := none
  domain? : Option (Array Json) := none
  allowDataOverflow : Bool := false
  type : AxisType := .number
  /-- Axis label - can be a string or object with value, position, offset, etc. -/
  label? : Option Json := none
  deriving FromJson, ToJson

/-- XAxis with label support. -/
def LabeledXAxis : Component LabeledAxisProps where
  javascript := Recharts.javascript
  «export» := "XAxis"

/-- Props for chart error boundary (empty, uses children only). -/
structure ChartErrorBoundaryProps where
  deriving Server.RpcEncodable

/-- Error boundary that catches React/Recharts errors and renders nothing instead of error message. -/
@[widget_module]
def ChartErrorBoundary : Component ChartErrorBoundaryProps where
  javascript := "
import * as React from 'react';
class E extends React.Component {
  state = { e: false };
  static getDerivedStateFromError = () => ({ e: true });
  render = () => this.state.e ? null : this.props.children;
}
export default (p) => React.createElement(E, null, p.children);
"

/-- RPC method to cancel a model checker instance by setting its cancel token. -/
@[server_rpc_method]
def cancelModelCheck (instanceId : Nat) : RequestM (RequestTask Unit) := RequestM.asTask do
  requestCancellation instanceId

/-- Props for the Stop button widget. -/
structure StopButtonProps where
  instanceId : Nat
  /-- Changes on handoff to reset button state. -/
  resetKey : Nat
  deriving Server.RpcEncodable

/-- Stop button widget that calls the cancelModelCheck RPC method. -/
@[widget_module]
def StopButton : Component StopButtonProps where
  javascript := "
import { useRpcSession } from '@leanprover/infoview';
import * as React from 'react';

export default function StopButton(props) {
  const rs = useRpcSession();
  const [stopping, setStopping] = React.useState(false);

  // Reset stopping state when resetKey changes (e.g., on handoff)
  React.useEffect(() => { setStopping(false); }, [props.resetKey]);

  const handleStop = async () => {
    setStopping(true);
    try {
      await rs.call('Veil.ModelChecker.cancelModelCheck', props.instanceId);
    } catch (e) {
      console.error('Failed to cancel model check:', e);
    }
  };

  return React.createElement('button', {
    onClick: handleStop,
    disabled: stopping,
    style: {
      padding: '4px 12px',
      cursor: stopping ? 'not-allowed' : 'pointer',
      backgroundColor: stopping ? '#999' : '#cc3333',
      color: 'white',
      border: 'none',
      borderRadius: '4px',
      fontSize: '12px',
      fontWeight: 'bold'
    }
  }, stopping ? 'Stopping...' : 'Stop');
}
"

/-- Decomposed time from milliseconds. -/
private structure TimeComponents where
  hours : Nat
  minutes : Nat
  seconds : Nat
  millis : Nat

/-- Decompose milliseconds into hours, minutes, seconds, and remaining millis. -/
private def decomposeTime (ms : Nat) : TimeComponents :=
  let totalSeconds := ms / 1000
  ⟨totalSeconds / 3600, (totalSeconds % 3600) / 60, totalSeconds % 60, ms % 1000⟩

/-- Format elapsed milliseconds as a human-readable string. -/
def formatElapsedTime (ms : Nat) : String :=
  let t := decomposeTime ms
  if t.hours > 0 then
    s!"{t.hours}h {t.minutes}m {t.seconds}s"
  else if t.minutes > 0 then
    s!"{t.minutes}m {t.seconds}.{t.millis / 100}s"
  else
    s!"{t.seconds}.{t.millis / 100}s"

/-- Generate status text including compilation info. -/
private def statusWithCompilation (p : Progress) : String :=
  match p.compilationStatus with
  | .inProgress ms _ => s!"{p.status} (compiling: {formatElapsedTime ms})"
  | .failed _ => s!"{p.status} (compilation failed)"
  | _ => p.status

/-- Generate HTML for compilation failure message with details. -/
private def compilationFailureHtml (err : String) : Html :=
  <details style={json% {"marginTop": "8px"}}>
    <summary style={json% {"color": "#cc6600", "cursor": "pointer", "fontSize": "12px"}}>
      Compilation failed - continuing with interpreted mode (click for details)
    </summary>
    <pre style={json% {"whiteSpace": "pre-wrap", "wordBreak": "break-word", "fontFamily": "monospace", "fontSize": "11px", "margin": "8px 0", "padding": "8px", "backgroundColor": "var(--vscode-textBlockQuote-background, #222)", "borderRadius": "4px", "maxHeight": "200px", "overflow": "auto"}}>
      {.text err}
    </pre>
  </details>

/-- Generate HTML for a single log line. -/
private def logLineHtml (line : Concrete.CompilationLogLine) : Html := Id.run do
  let timeStr := formatElapsedTime line.timestamp
  let contentStyle := if line.isError
    then json% {"color": "#ff8888"}
    else json% {"color": "#cccccc"}
  return <div style={json% {"fontFamily": "monospace", "fontSize": "10px", "whiteSpace": "pre-wrap", "wordBreak": "break-all"}}>
    <span style={json% {"color": "#666", "marginRight": "8px"}}>[{.text timeStr}]</span>
    <span style={contentStyle}>{.text line.content}</span>
  </div>

/-- Generate HTML for live compilation log during compilation. -/
private def compilationLogHtml (elapsedMs : Nat) (logLines : Array Concrete.CompilationLogLine) : Html :=
  <details style={json% {"marginTop": "8px"}}>
    <summary style={json% {"color": "var(--vscode-descriptionForeground)", "cursor": "pointer", "fontSize": "12px"}}>
      Compilation log ({.text (toString logLines.size)} lines, {.text (formatElapsedTime elapsedMs)})
    </summary>
    <div style={json% {
      "marginTop": "4px",
      "padding": "8px",
      "backgroundColor": "var(--vscode-textBlockQuote-background, #1e1e1e)",
      "borderRadius": "4px",
      "maxHeight": "300px",
      "overflow": "auto"
    }}>
      {.element "div" #[] (logLines.map logLineHtml)}
    </div>
  </details>

/-- Common style for right-aligned text. -/
private def rightAlignStyle : Json := json% {"textAlign": "right"}

private def statRow (label value : String) : Html :=
  <tr>
    <td style={json% {"paddingRight": "12px"}}>{.text label}</td>
    <td style={rightAlignStyle}>{.text value}</td>
  </tr>

/-- Split action name into base name and arguments (everything after first space). -/
private def splitActionName (name : String) : String × String :=
  match name.splitOn " " with
  | [] => (name, "")
  | [base] => (base, "")
  | base :: rest => (base, " ".intercalate rest)

/-- Grouped action statistics for display. -/
structure ActionGroup where
  baseName : String
  totalGenerated : Nat
  totalDistinct : Nat
  variants : List ActionStatDisplay
  deriving Inhabited

/-- Group action stats by their base name. -/
private def groupActionStats (stats : List ActionStatDisplay) : List ActionGroup :=
  let grouped := stats.foldl (init := (Std.HashMap.emptyWithCapacity : Std.HashMap String ActionGroup)) fun acc stat =>
    let (base, _) := splitActionName stat.name
    match acc[base]? with
    | some group => acc.insert base ⟨
        group.baseName,
        group.totalGenerated + stat.statesGenerated,
        group.totalDistinct + stat.distinctStates,
        stat :: group.variants
      ⟩
    | none => acc.insert base ⟨
        base,
        stat.statesGenerated,
        stat.distinctStates,
        [stat]
      ⟩
  grouped.toList.map (·.2)
    |>.map (fun g => ⟨g.baseName, g.totalGenerated, g.totalDistinct, g.variants.reverse.mergeSort (·.name < ·.name)⟩)
    |>.mergeSort (·.baseName < ·.baseName)

/-- Base grid row style for action coverage. -/
private def gridRowBaseStyle : Json := json% {"display": "grid", "gridTemplateColumns": "1fr 70px 60px", "gap": "8px", "padding": "2px 0"}

/-- Grid row style for consistent alignment. Highlighted if action was never enabled. -/
private def gridRowStyle (highlight : Bool := false) : Json :=
  if highlight then json% {"display": "grid", "gridTemplateColumns": "1fr 70px 60px", "gap": "8px", "padding": "2px 0", "backgroundColor": "#554400"}
  else gridRowBaseStyle

/-- Style for variant sub-items (right-aligned, muted). -/
private def variantNumStyle : Json := json% {"textAlign": "right", "color": "#aaa", "fontSize": "10px"}

/-- Render a single variant row (for expanded view). -/
private def variantRow (stat : ActionStatDisplay) : Html :=
  let (_, args) := splitActionName stat.name
  let displayName := if args.isEmpty then "(no args)" else args
  .element "div" #[("style", gridRowStyle (stat.statesGenerated == 0))] #[
    .element "span" #[("style", json% {"paddingLeft": "16px", "color": "#aaa", "fontSize": "10px"})] #[.text displayName],
    .element "span" #[("style", variantNumStyle)] #[.text (toString stat.statesGenerated)],
    .element "span" #[("style", variantNumStyle)] #[.text (toString stat.distinctStates)]
  ]

/-- Render an action group as Html. For multi-variant groups, uses details/summary. -/
private def actionGroupHtml (group : ActionGroup) : Html := Id.run do
  let rowStyle := gridRowStyle (group.totalGenerated == 0)
  if group.variants.length == 1 then
    return <div style={rowStyle}>
      <span>{.text group.baseName}</span>
      <span style={rightAlignStyle}>{.text (toString group.totalGenerated)}</span>
      <span style={rightAlignStyle}>{.text (toString group.totalDistinct)}</span>
    </div>
  else
    return <details>
      <summary style={rowStyle}>
        <span style={json% {"cursor": "pointer"}}>{.text group.baseName}</span>
        <span style={rightAlignStyle}>{.text (toString group.totalGenerated)}</span>
        <span style={rightAlignStyle}>{.text (toString group.totalDistinct)}</span>
      </summary>
      <div>
        {.element "span" #[] (group.variants.map variantRow).toArray}
      </div>
    </details>

/-- Get list of never-enabled action names from groups and all action labels. -/
private def getNeverEnabledActions (groups : List ActionGroup) (allActionLabels : List String) : List String :=
  let zeroInGroups := groups.filter (·.totalGenerated == 0) |>.map (·.baseName)
  let groupBaseNames := groups.map (·.baseName)
  let missingFromGroups := allActionLabels.filter (fun l => !groupBaseNames.contains l)
  (zeroInGroups ++ missingFromGroups).mergeSort (· < ·)

/-- Render warning for actions that were never enabled. -/
private def neverEnabledWarning (neverEnabled : List String) : Html :=
  if neverEnabled.isEmpty then .text ""
  else
    let warningStyle := json% {"color": "#cc6600", "fontSize": "11px", "marginTop": "6px", "padding": "4px 8px", "backgroundColor": "#332200", "borderRadius": "4px"}
    .element "div" #[("style", warningStyle)] #[
      .text s!"⚠ Never enabled: {", ".intercalate neverEnabled}"
    ]

/-- Style for right-aligned bold header text. -/
private def rightBoldStyle : Json := json% {"textAlign": "right", "fontWeight": "bold"}

/-- Render action coverage with grouped actions using CSS Grid. -/
private def actionCoverageHtml (actionStats : List ActionStatDisplay) (allActionLabels : List String) : Html := Id.run do
  if actionStats.isEmpty && allActionLabels.isEmpty then return .text ""
  let groups := groupActionStats actionStats
  let neverEnabled := getNeverEnabledActions groups allActionLabels
  let warningText := if neverEnabled.isEmpty then "" else s!" — {neverEnabled.length} never enabled ⚠"
  let headerStyle := json% {"display": "grid", "gridTemplateColumns": "1fr 70px 60px", "gap": "8px", "padding": "2px 0", "borderBottom": "1px solid #444", "marginBottom": "4px"}
  return <details style={json% {"marginTop": "8px"}}>
    <summary style={json% {"cursor": "pointer", "fontSize": "12px", "color": "var(--vscode-descriptionForeground)"}}>
      Action Coverage ({.text (s!"{groups.length} actions")}{.element "span" #[("style", json% {"color": "#cc6600"})] #[.text warningText]})
    </summary>
    <div style={json% {"marginTop": "4px", "fontSize": "11px"}}>
      <div style={headerStyle}>
        <span style={json% {"fontWeight": "bold"}}>Action</span>
        <span style={rightBoldStyle}>Generated</span>
        <span style={rightBoldStyle}>Distinct</span>
      </div>
      <div>{.element "span" #[] (groups.map actionGroupHtml).toArray}</div>
      {neverEnabledWarning neverEnabled}
    </div>
  </details>

/-! ## Progress History Charts -/

/-- Props for metrics history toggle (table vs graph view with JSON export). -/
structure MetricsHistoryToggleProps where
  historyJson : String
  deriving Server.RpcEncodable

/-- Toggle widget for switching between table and graph views, with JSON copy functionality. -/
@[widget_module]
def MetricsHistoryToggle : Component MetricsHistoryToggleProps where
  javascript := "
import * as React from 'react';

export default function MetricsHistoryToggle(props) {
  const [view, setView] = React.useState('graph');
  const [copied, setCopied] = React.useState(false);
  const tableRef = React.useRef(null);

  const copyJson = () => {
    navigator.clipboard.writeText(props.historyJson).then(() => {
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    });
  };

  // Auto-scroll table to bottom when data changes
  React.useEffect(() => {
    if (tableRef.current && view === 'table') {
      const scrollContainer = tableRef.current.querySelector('div[style*=\"overflow\"]');
      if (scrollContainer) {
        scrollContainer.scrollTop = scrollContainer.scrollHeight;
      }
    }
  }, [props.historyJson, view]);

  const children = React.Children.toArray(props.children);
  const tableView = children[0];
  const graphView = children[1];

  const buttonStyle = (active) => ({
    padding: '4px 8px',
    border: active ? 'none' : '1px solid var(--vscode-button-border, transparent)',
    borderRadius: '4px',
    cursor: 'pointer',
    backgroundColor: active ? 'var(--vscode-button-background)' : 'var(--vscode-button-secondaryBackground)',
    color: active ? 'var(--vscode-button-foreground)' : 'var(--vscode-button-secondaryForeground)',
    fontSize: '11px'
  });

  return React.createElement('div', {},
    React.createElement('div', { style: { marginBottom: '8px', display: 'flex', gap: '4px', justifyContent: 'space-between' } },
      React.createElement('div', { style: { display: 'flex', gap: '4px' } },
        React.createElement('button', { onClick: () => setView('graph'), style: buttonStyle(view === 'graph') }, 'Graph'),
        React.createElement('button', { onClick: () => setView('table'), style: buttonStyle(view === 'table') }, 'Table')
      ),
      React.createElement('button', { onClick: copyJson, style: buttonStyle(false) },
        copied ? 'Copied!' : 'Copy JSON')
    ),
    React.createElement('div', { ref: tableRef, style: { display: view === 'table' ? 'block' : 'none' } }, tableView),
    React.createElement('div', { style: { display: view === 'graph' ? 'block' : 'none' } }, graphView)
  );
}
"

/-- Count the number of digits in a natural number. -/
private def numDigits (n : Nat) : Nat :=
  if n < 10 then 1 else 1 + numDigits (n / 10)

/-- Calculate the left margin for a chart based on the maximum Y value.
    Each digit needs approximately 8px, plus a small base margin.
    Capped at 100 to ensure chart area remains positive (chart width=350, right margin=20). -/
private def calcLeftMargin (maxValue : Nat) : Nat :=
  let digits := numDigits maxValue
  min 100 (10 + digits * 8)

/-- Chart configuration for a single metric. -/
structure ChartConfig where
  title : String
  color : String
  getValue : ProgressHistoryPoint → Nat

/-- Convert history to JSON format for a chart. Uses "value" as the Y-axis key. -/
private def historyToChartData (history : Array ProgressHistoryPoint) (getValue : ProgressHistoryPoint → Nat) : Array Json :=
  history.map fun point => json% {
    time: $(point.timestamp / 1000),
    value: $(getValue point)
  }

/-- Render a single chart with the given configuration. -/
private def renderChart (history : Array ProgressHistoryPoint) (leftMargin : Nat) (config : ChartConfig) : Html := Id.run do
  let data := historyToChartData history config.getValue
  return <div style={json% {"marginBottom": "12px"}}>
    <div style={json% {"fontSize": "11px", "color": "var(--vscode-descriptionForeground)", "marginBottom": "4px"}}>
      {.text config.title}
    </div>
    <LineChart width={350} height={140} data={data} margin={⟨10, 20, 20, leftMargin⟩}>
      <LabeledXAxis dataKey?="time" type={.number} label?={json% {"value": "Time (s)", "position": "bottom", "offset": 0, "fontSize": 10}} />
      <YAxis type={.number} />
      <Tooltip />
      <Line type={.monotone} dataKey="value" stroke={config.color} dot?={true} />
    </LineChart>
  </div>

/-- Chart configurations for all metrics in display order. -/
private def chartConfigs : Array ChartConfig := #[
  ⟨"Diameter", "#9C27B0", (·.diameter)⟩,
  ⟨"States Found", "#4CAF50", (·.statesFound)⟩,
  ⟨"Distinct States", "#2196F3", (·.distinctStates)⟩,
  ⟨"Queue Size", "#FF9800", (·.queue)⟩
]

/-- Format milliseconds as HH:MM:SS (TLC-style). -/
private def formatTimeHMS (ms : Nat) : String :=
  let t := decomposeTime ms
  let pad (n : Nat) : String := if n < 10 then s!"0{n}" else toString n
  s!"{pad t.hours}:{pad t.minutes}:{pad t.seconds}"

/-- Common style for table cells. -/
private def tableCellStyle : Json := json% {"padding": "4px 8px", "textAlign": "right"}

/-- Create a table header cell. -/
private def th (text : String) : Html :=
  .element "th" #[("style", json% {"padding": "4px 8px", "textAlign": "right", "fontWeight": "bold"})] #[.text text]

/-- Create a table data cell. -/
private def td (text : String) : Html :=
  .element "td" #[("style", tableCellStyle)] #[.text text]

/-- Render a single row in the history table. -/
private def historyTableRow (point : ProgressHistoryPoint) : Html :=
  .element "tr" #[("style", json% {"borderBottom": "1px solid var(--vscode-panel-border)"})] #[
    .element "td" #[("style", json% {"padding": "4px 8px", "textAlign": "right", "fontFamily": "monospace"})] #[.text (formatTimeHMS point.timestamp)],
    td (toString point.diameter), td (toString point.statesFound),
    td (toString point.distinctStates), td (toString point.queue)
  ]

/-- Render the history as a table view (TLC-style). -/
private def renderTableView (history : Array ProgressHistoryPoint) : Html := Id.run do
  let headerStyle := json% {"borderBottom": "1px solid var(--vscode-panel-border)", "position": "sticky", "top": "0", "backgroundColor": "var(--vscode-textBlockQuote-background)"}
  let headerRow : Html := .element "tr" #[("style", headerStyle)] #[th "Time", th "Diameter", th "Found", th "Distinct", th "Queue"]
  let tableRows := #[headerRow] ++ history.map historyTableRow
  return <div style={json% {"maxHeight": "300px", "overflow": "auto"}}>
    <table style={json% {"borderCollapse": "collapse", "fontSize": "11px", "width": "100%"}}>
      {.element "tbody" #[] tableRows}
    </table>
  </div>

/-- Render the history as graphs. -/
private def renderGraphView (history : Array ProgressHistoryPoint) (leftMargin : Nat) : Html :=
  let charts := chartConfigs.map fun config =>
    Html.ofComponent ChartErrorBoundary ⟨⟩ #[renderChart history leftMargin config]
  .element "div" #[] charts

/-- Convert history to JSON string for export. -/
private def historyToJsonString (history : Array ProgressHistoryPoint) : String :=
  let rows := history.map fun p => json% {
    timeMs: $(p.timestamp),
    timeStr: $(formatTimeHMS p.timestamp),
    diameter: $(p.diameter),
    statesFound: $(p.statesFound),
    distinctStates: $(p.distinctStates),
    queue: $(p.queue)
  }
  toString (toJson rows)

/-- Render the metrics history section (collapsible) with table/graph toggle. -/
private def metricsHistoryHtml (history : Array ProgressHistoryPoint) : Html := Id.run do
  if history.size < 2 then return .text ""  -- Need at least 2 points for a chart
  let pointCount := history.size
  let timeRange := match (history[0]?, history[history.size - 1]?) with
    | (some first, some last) => formatElapsedTime (last.timestamp - first.timestamp)
    | _ => "0s"
  -- Calculate left margin based on the largest value across all metrics
  let maxVal := history.foldl (fun acc p =>
    max acc (max p.diameter (max p.statesFound (max p.distinctStates p.queue)))) 0
  let leftMargin := calcLeftMargin maxVal
  -- Create table and graph views
  let tableView := renderTableView history
  let graphView := renderGraphView history leftMargin
  let historyJson := historyToJsonString history
  return <details style={json% {"marginTop": "8px"}}>
    <summary style={json% {"cursor": "pointer", "fontSize": "12px", "color": "var(--vscode-descriptionForeground)"}}>
      Metrics History ({.text (toString pointCount)} samples, {.text timeRange})
    </summary>
    <div style={json% {"marginTop": "4px", "fontSize": "11px"}}>
      {Html.ofComponent MetricsHistoryToggle ⟨historyJson⟩ #[tableView, graphView]}
    </div>
  </details>

/-- Convert Progress to Html for display, with optional Stop button. Uses TLC-style terminology. -/
def progressToHtml (p : Progress) (instanceId? : Option Nat := none) : Html :=
  <div className="model-checker-progress" style={json% {"fontFamily": "monospace", "padding": "8px"}}>
    {if p.isRunning then
      <div style={json% {"marginTop": "8px", "display": "flex", "alignItems": "center", "gap": "12px"}}>
        <div style={json% {"color": "#0066cc"}}>
          <i>{.text (statusWithCompilation p)}</i>
        </div>
        {match instanceId? with
         | some id => Html.ofComponent StopButton ⟨id, p.startTimeMs⟩ #[]
         | none => .text ""}
      </div>
    else if p.isCancelled then
      <div style={json% {"marginTop": "8px", "color": "#cc6600", "fontWeight": "bold"}}>
        Cancelled
      </div>
    else
      <div style={json% {"marginTop": "8px"}}>
        <div style={json% {"color": "#00aa00", "fontWeight": "bold"}}>Done!</div>
      </div>}
    <table style={json% {"borderCollapse": "collapse"}}>
      <tbody>
        {statRow "Diameter:" (toString p.diameter)}
        {statRow "States Found:" (toString p.statesFound)}
        {statRow "Distinct States:" (toString p.distinctStates)}
        {statRow "Queue:" (toString p.queue)}
        {statRow "Elapsed time:" (formatElapsedTime p.elapsedMs)}
      </tbody>
    </table>
    {metricsHistoryHtml p.history}
    {actionCoverageHtml p.actionStats p.allActionLabels}
    {match p.compilationStatus with
     | .inProgress ms lines => if lines.isEmpty then .text "" else compilationLogHtml ms lines
     | .failed err => compilationFailureHtml err
     | _ => .text ""}
  </div>

/-- Display a widget with the given HTML. -/
private def displayWidget (atStx : Syntax) (html : Html) : CommandElabM Unit := do
  liftCoreM <| Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.rpcEncode html) })
    atStx

/-- Check if the JSON contains an error field and extract it. -/
private def extractError (json : Json) : Option String :=
  json.getObjValAs? String "error" |>.toOption

/-- Check if JSON has valid trace data (not null/empty). -/
private def hasTraceData : Json → Bool
  | .obj obj => !obj.isEmpty
  | _ => false

/-- Render an error box with the given message. -/
private def errorBox (errorMsg : String) : Html :=
  <div style={json% {"padding": "12px", "margin": "8px", "backgroundColor": "var(--vscode-inputValidation-errorBackground, #5a1d1d)", "border": "1px solid var(--vscode-inputValidation-errorBorder, #be1100)", "borderRadius": "6px"}}>
    <div style={json% {"fontWeight": "bold", "marginBottom": "8px", "color": "var(--vscode-errorForeground, #f48771)"}}>
      {.text "Error"}
    </div>
    <pre style={json% {"whiteSpace": "pre-wrap", "wordBreak": "break-word", "fontFamily": "monospace", "fontSize": "12px", "margin": "0", "color": "var(--vscode-editor-foreground)"}}>
      {.text errorMsg}
    </pre>
  </div>

private def noResultData : Html :=
  <div style={json% {"color": "#cc6600"}}><i>No result data available</i></div>

/-- Create the final result display with both progress summary and result viewer. -/
def mkFinalResultHtml (p : Progress) (resultJson : Option Json) : Html :=
  <div className="model-checker-result">
    {progressToHtml p}
    {match resultJson with
     | some json =>
       match extractError json with
       | some errorMsg => errorBox errorMsg
       | none => if hasTraceData json then Html.ofComponent TraceDisplayViewer ⟨json, "vertical", none⟩ #[] else noResultData
     | none => noResultData}
  </div>

/-- Create a streaming progress widget that polls progress by instance ID. -/
def mkProgressWidget (instanceId : Nat) : CoreM Html := do
  mkRefreshComponent (.text "Starting model checker...") (getProgressStep instanceId)
where
  getProgressStep (id : Nat) : CoreM RefreshComponent.RefreshStep := do
    IO.sleep 100
    let progress ← getProgress id
    if progress.isRunning then
      return .cont (progressToHtml progress (some id))
    else
      return .last (mkFinalResultHtml progress (← getResultJson id))

/-- Display a streaming progress widget at the given syntax. -/
def displayStreamingProgress (atStx : Syntax) (instanceId : Nat) : CommandElabM Unit := do
  let html ← liftCoreM (mkProgressWidget instanceId)
  displayWidget atStx html

end Veil.ModelChecker
