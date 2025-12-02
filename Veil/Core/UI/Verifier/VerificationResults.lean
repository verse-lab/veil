import Lean.Server.Rpc.Basic
import Lean.Elab.Command

import ProofWidgets.Component.Basic
import ProofWidgets.Component.HtmlDisplay
import Veil.Core.UI.Widget.RefreshComponent
import Veil.Frontend.DSL.Infra.Metadata
import Veil.Core.Tools.Verifier.Results

section

namespace ProofWidgets
open Lean Server

open Veil in
structure VerificationResultsProps where
  /-- The verification results to display. -/
  results : VerificationResults VCMetadata SmtResult
deriving Server.RpcEncodable


@[widget_module]
def VerificationResultsViewer : Component VerificationResultsProps where
  javascript := include_str "." / "verificationResults.js"

end ProofWidgets

namespace Veil.Verifier

open Lean Elab Command ProofWidgets RefreshComponent

inductive StreamingStatus where
  | running
  | done
deriving Inhabited, Server.RpcEncodable

private def displayWidget (atStx : Syntax) (html : Html) : CommandElabM Unit := do
  liftCoreM <| Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.rpcEncode html) })
    atStx

def displayResults (atStx : Syntax) (results : VerificationResults VCMetadata SmtResult) : CommandElabM Unit := do
  let html := Html.ofComponent VerificationResultsViewer {results := results} #[]
  displayWidget atStx html

partial def displayStreamingResults (atStx : Syntax) (getter : CoreM (VerificationResults VCMetadata SmtResult × StreamingStatus)) : CommandElabM Unit := do
  let html ← liftCoreM <| mkRefreshComponentM (.text "Loading...") getStreamingResults
  displayWidget atStx html
  where
  getStreamingResults : CoreM (RefreshStep CoreM) := do
    IO.sleep 100
    Core.checkSystem "getStreamingResults"
    let (results, status) ← getter
    let html := Html.ofComponent VerificationResultsViewer {results := results} #[]
    match status with
    | .running => return .cont html getStreamingResults
    | .done => return .last html




end Veil.Verifier
