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

/-- Props for the model checker progress viewer widget. -/
structure ProgressViewerProps where
  /-- The progress state to display. -/
  progress : Progress
deriving Server.RpcEncodable

/-- Convert Progress to Html for display. -/
def progressToHtml (p : Progress) : Html :=
  <div className="model-checker-progress" style={json% {"fontFamily": "monospace", "padding": "8px"}}>
    {if p.isRunning then
      <div style={json% {"marginTop": "8px", "color": "#0066cc"}}>
        <i>Running...</i>
      </div>
    else
      <div style={json% {"marginTop": "8px", "color": "#00aa00", "fontWeight": "bold"}}>
        Done!
    </div>}
    <table style={json% {"borderCollapse": "collapse"}}>
      <tbody>
        <tr>
          <td style={json% {"paddingRight": "12px"}}>States processed:</td>
          <td style={json% {"textAlign": "right"}}>{.text (toString p.statesProcessed)}</td>
        </tr>
        <tr>
          <td style={json% {"paddingRight": "12px"}}>Unique states:</td>
          <td style={json% {"textAlign": "right"}}>{.text (toString p.uniqueStates)}</td>
        </tr>
        <tr>
          <td style={json% {"paddingRight": "12px"}}>Completed depth:</td>
          <td style={json% {"textAlign": "right"}}>{.text (toString p.completedDepth)}</td>
        </tr>
        <tr>
          <td style={json% {"paddingRight": "12px"}}>Current depth:</td>
          <td style={json% {"textAlign": "right"}}>{.text (toString p.currentDepth)}</td>
        </tr>
        <tr>
          <td style={json% {"paddingRight": "12px"}}>Queue length:</td>
          <td style={json% {"textAlign": "right"}}>{.text (toString p.queueLength)}</td>
        </tr>
        <tr>
          <td style={json% {"paddingRight": "12px"}}>Elapsed time:</td>
          <td style={json% {"textAlign": "right"}}>{.text (formatElapsedTime p.elapsedMs)}</td>
        </tr>
      </tbody>
    </table>
  </div>

/-- Display a widget with the given HTML. -/
private def displayWidget (atStx : Syntax) (html : Html) : CommandElabM Unit := do
  liftCoreM <| Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.rpcEncode html) })
    atStx

/-- Create the final result display with both progress summary and result viewer. -/
def mkFinalResultHtml (p : Progress) (resultJson : Option Json) : Html :=
  <div className="model-checker-result">
    {progressToHtml p}
    {match resultJson with
     | some json =>
       Html.ofComponent TraceDisplayViewer ⟨json, "vertical"⟩ #[]
     | none =>
       <div style={json% {"color": "#cc6600"}}>
         <i>No result data available</i>
       </div>}
  </div>

/-- Create a streaming progress widget that polls progress by instance ID. -/
partial def mkProgressWidget (instanceId : Nat) : CoreM Html := do
  mkRefreshComponentM (.text "Starting model checker...") (getProgressStep instanceId)
where
  getProgressStep (id : Nat) : CoreM (RefreshStep CoreM) := do
    IO.sleep 100  -- Poll every 100ms
    Core.checkSystem "getProgressStep"
    let progress ← getProgress id
    if progress.isRunning then
      return .cont (progressToHtml progress) (getProgressStep id)
    else
      -- When done, fetch the result JSON and display it
      let resultJson ← getResultJson id
      return .last (mkFinalResultHtml progress resultJson)

/-- Display a streaming progress widget at the given syntax. -/
def displayStreamingProgress (atStx : Syntax) (instanceId : Nat) : CommandElabM Unit := do
  let html ← liftCoreM (mkProgressWidget instanceId)
  displayWidget atStx html

end Veil.ModelChecker
