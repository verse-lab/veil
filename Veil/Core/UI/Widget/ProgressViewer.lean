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

namespace Veil.ModelChecker

open Lean Server Elab Command ProofWidgets Jsx Veil.ModelChecker.Concrete RefreshComponent

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

/-- Format elapsed milliseconds as a human-readable string. -/
def formatElapsedTime (ms : Nat) : String :=
  let totalSeconds := ms / 1000
  let millis := ms % 1000
  let hours := totalSeconds / 3600
  let minutes := (totalSeconds % 3600) / 60
  let seconds := totalSeconds % 60
  if hours > 0 then
    s!"{hours}h {minutes}m {seconds}s"
  else if minutes > 0 then
    s!"{minutes}m {seconds}.{millis / 100}s"
  else
    s!"{seconds}.{millis / 100}s"

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
    <summary style={json% {"color": "#888", "cursor": "pointer", "fontSize": "12px"}}>
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

private def statRow (label value : String) : Html :=
  <tr>
    <td style={json% {"paddingRight": "12px"}}>{.text label}</td>
    <td style={json% {"textAlign": "right"}}>{.text value}</td>
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

/-- Grid row style for consistent alignment. Highlighted if action was never enabled. -/
private def gridRowStyle (highlight : Bool := false) : Json :=
  if highlight then json% {"display": "grid", "gridTemplateColumns": "1fr 70px 60px", "gap": "8px", "padding": "2px 0", "backgroundColor": "#554400"}
  else json% {"display": "grid", "gridTemplateColumns": "1fr 70px 60px", "gap": "8px", "padding": "2px 0"}

/-- Render a single variant row (for expanded view). -/
private def variantRow (stat : ActionStatDisplay) : Html :=
  let (_, args) := splitActionName stat.name
  let displayName := if args.isEmpty then "(no args)" else args
  let subStyle : Json := json% {"paddingLeft": "16px", "color": "#aaa", "fontSize": "10px"}
  .element "div" #[("style", gridRowStyle (stat.statesGenerated == 0))] #[
    .element "span" #[("style", subStyle)] #[.text displayName],
    .element "span" #[("style", json% {"textAlign": "right", "color": "#aaa", "fontSize": "10px"})] #[.text (toString stat.statesGenerated)],
    .element "span" #[("style", json% {"textAlign": "right", "color": "#aaa", "fontSize": "10px"})] #[.text (toString stat.distinctStates)]
  ]

/-- Render an action group as Html. For multi-variant groups, uses details/summary. -/
private def actionGroupHtml (group : ActionGroup) : Html := Id.run do
  let rowStyle := gridRowStyle (group.totalGenerated == 0)
  if group.variants.length == 1 then
    -- Single variant: just show one row
    return <div style={rowStyle}>
      <span>{.text group.baseName}</span>
      <span style={json% {"textAlign": "right"}}>{.text (toString group.totalGenerated)}</span>
      <span style={json% {"textAlign": "right"}}>{.text (toString group.totalDistinct)}</span>
    </div>
  else
    -- Multiple variants: use details element
    return <details>
      <summary style={rowStyle}>
        <span style={json% {"cursor": "pointer"}}>{.text group.baseName}</span>
        <span style={json% {"textAlign": "right"}}>{.text (toString group.totalGenerated)}</span>
        <span style={json% {"textAlign": "right"}}>{.text (toString group.totalDistinct)}</span>
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

/-- Render action coverage with grouped actions using CSS Grid. -/
private def actionCoverageHtml (actionStats : List ActionStatDisplay) (allActionLabels : List String) : Html := Id.run do
  if actionStats.isEmpty && allActionLabels.isEmpty then return .text ""
  let groups := groupActionStats actionStats
  let neverEnabled := getNeverEnabledActions groups allActionLabels
  let numGroups := groups.length
  let actionCountText := s!"{numGroups} actions"
  let warningText := if neverEnabled.isEmpty then "" else s!" — {neverEnabled.length} never enabled ⚠"
  let headerStyle := json% {"display": "grid", "gridTemplateColumns": "1fr 70px 60px", "gap": "8px", "padding": "2px 0", "borderBottom": "1px solid #444", "marginBottom": "4px"}
  return <details style={json% {"marginTop": "8px"}}>
    <summary style={json% {"cursor": "pointer", "fontSize": "12px", "color": "#888"}}>
      Action Coverage ({.text actionCountText}{.element "span" #[("style", json% {"color": "#cc6600"})] #[.text warningText]})
    </summary>
    <div style={json% {"marginTop": "4px", "fontSize": "11px"}}>
      <div style={headerStyle}>
        <span style={json% {"fontWeight": "bold"}}>Action</span>
        <span style={json% {"textAlign": "right", "fontWeight": "bold"}}>Generated</span>
        <span style={json% {"textAlign": "right", "fontWeight": "bold"}}>Distinct</span>
      </div>
      <div>
        {.element "span" #[] (groups.map actionGroupHtml).toArray}
      </div>
      {neverEnabledWarning neverEnabled}
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
