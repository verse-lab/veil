import Lean.Server.Rpc.Basic
import Lean.Elab.Command
import Lean.PrettyPrinter

import ProofWidgets.Component.Basic
import ProofWidgets.Component.HtmlDisplay
import Veil.Core.UI.Widget.RefreshComponent
import Veil.Frontend.DSL.Infra.Metadata
import Veil.Core.Tools.Verifier.Results
import Veil.Core.Tools.Verifier.Server

section

namespace ProofWidgets
open Lean Server

open Veil in
structure VerificationResultsProps where
  /-- The verification results to display. -/
  results : VerificationResults VCMetadata SmtResult
  /-- Position after #check_invariants for theorem insertion (line, character). -/
  insertPosition : Lsp.Position
  /-- Document URI for edit operations. -/
  documentUri : String
deriving Server.RpcEncodable


@[widget_module]
def VerificationResultsViewer : Component VerificationResultsProps where
  javascript := include_str ".." / ".." / ".." / ".." / ".lake" / "build" / "js" / "verificationResults.js"

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

/-- Compute the insert position (line after the syntax) and document URI. -/
private def getInsertInfo (atStx : Syntax) : CommandElabM (Lsp.Position × String) := do
  let fileMap ← getFileMap
  let docUri := (← getFileName)
  -- Get position at end of the syntax, then move to start of next line
  let some tailPos := atStx.getTailPos? | return ({ line := 0, character := 0 }, docUri)
  let pos := fileMap.toPosition tailPos
  -- Insert at the start of the line after the command
  let insertPos : Lsp.Position := { line := pos.line, character := 0 }
  return (insertPos, docUri)

def displayResults (atStx : Syntax) (results : VerificationResults VCMetadata SmtResult) : CommandElabM Unit := do
  let (insertPosition, documentUri) ← getInsertInfo atStx
  let html := Html.ofComponent VerificationResultsViewer {results, insertPosition, documentUri} #[]
  displayWidget atStx html

partial def displayStreamingResults (atStx : Syntax) (getter : CoreM (VerificationResults VCMetadata SmtResult × StreamingStatus)) : CommandElabM Unit := do
  let (insertPosition, documentUri) ← getInsertInfo atStx
  let html ← liftCoreM <| mkRefreshComponentM (.text "Loading...") (getStreamingResults insertPosition documentUri)
  displayWidget atStx html
  where
  getStreamingResults (insertPosition : Lsp.Position) (documentUri : String) : CoreM (RefreshStep CoreM) := do
    IO.sleep 100
    Core.checkSystem "getStreamingResults"
    let (results, status) ← getter
    let html := Html.ofComponent VerificationResultsViewer {results, insertPosition, documentUri} #[]
    match status with
    | .running => return .cont html (getStreamingResults insertPosition documentUri)
    | .done => return .last html

/-- Map VCStatus to emoji for text output. -/
def statusEmoji (status : Option VCStatus) : String :=
  match status with
  | some .proven => "✅"
  | some .disproven => "❌"
  | some .unknown => "❓"
  | some .error => "💥"
  | none => "⏳"

/-- Format verification results as text output for logging. -/
def formatVerificationResults (results : VerificationResults VCMetadata SmtResult) : MessageData := Id.run do
  let vcs := results.vcs.filter fun vc =>
    vc.metadata.isInduction && !vc.isDormant && vc.alternativeFor.isNone
  let getAction := fun vc => match vc.metadata with | .induction m => m.action | _ => .anonymous
  let initVCs := vcs.filter (getAction · == `initializer)
  let actionGroups := vcs.filter (getAction · != `initializer) |>.foldl (init := Std.HashMap.emptyWithCapacity) fun acc vc =>
    acc.insert (getAction vc) (acc.getD (getAction vc) #[] |>.push vc)

  let mut msg := m!"Initialization must establish the invariant:\n"
  for vc in initVCs do
    let .induction m := vc.metadata | continue
    msg := msg ++ m!"  {m.property} ... {statusEmoji vc.status}\n"
  msg := msg ++ m!"The following set of actions must preserve the invariant and successfully terminate:\n"
  for (actionName, vcs) in actionGroups.toArray do
    msg := msg ++ m!"  {actionName}\n"
    for vc in vcs do
      let .induction m := vc.metadata | continue
      msg := msg ++ m!"    {m.property} ... {statusEmoji vc.status}\n"
  return msg

/-- Check if any VCs have non-proven status. -/
def hasFailedVCs (results : VerificationResults VCMetadata SmtResult) : Bool :=
  results.vcs.any fun vc =>
    vc.metadata.isInduction && !vc.isDormant && vc.alternativeFor.isNone &&
    vc.status != some .proven

end Veil.Verifier
