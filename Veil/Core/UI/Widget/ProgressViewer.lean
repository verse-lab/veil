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
  | .inProgress ms => s!"{p.status} (compiling: {formatElapsedTime ms})"
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

private def statRow (label value : String) : Html :=
  <tr>
    <td style={json% {"paddingRight": "12px"}}>{.text label}</td>
    <td style={json% {"textAlign": "right"}}>{.text value}</td>
  </tr>

/-- Convert Progress to Html for display, with optional Stop button. -/
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
        {statRow "States processed:" (toString p.statesProcessed)}
        {statRow "Unique states:" (toString p.uniqueStates)}
        {statRow "Completed depth:" (toString p.completedDepth)}
        {statRow "Current depth:" (toString p.currentDepth)}
        {statRow "Queue length:" (toString p.queueLength)}
        {statRow "Elapsed time:" (formatElapsedTime p.elapsedMs)}
      </tbody>
    </table>
    {match p.compilationStatus with
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
       | none => if hasTraceData json then Html.ofComponent TraceDisplayViewer ⟨json, "vertical"⟩ #[] else noResultData
     | none => noResultData}
  </div>

/-- Create a streaming progress widget that polls progress by instance ID. -/
partial def mkProgressWidget (instanceId : Nat) : CoreM Html := do
  mkRefreshComponentM (.text "Starting model checker...") (getProgressStep instanceId)
where
  getProgressStep (id : Nat) : CoreM (RefreshStep CoreM) := do
    IO.sleep 100
    Core.checkSystem "getProgressStep"
    let progress ← getProgress id
    if progress.isRunning then
      return .cont (progressToHtml progress (some id)) (getProgressStep id)
    else
      return .last (mkFinalResultHtml progress (← getResultJson id))

/-- Display a streaming progress widget at the given syntax. -/
def displayStreamingProgress (atStx : Syntax) (instanceId : Nat) : CommandElabM Unit := do
  let html ← liftCoreM (mkProgressWidget instanceId)
  displayWidget atStx html

end Veil.ModelChecker
