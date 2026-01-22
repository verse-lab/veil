import Lean.Server.Rpc.Basic
import Lean.Elab.Command
import Lean.PrettyPrinter

import Veil.Base
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

def displayStreamingResults (atStx : Syntax) (getter : CoreM (VerificationResults VCMetadata SmtResult × StreamingStatus)) : CommandElabM Unit := do
  let (insertPosition, documentUri) ← getInsertInfo atStx
  let html ← liftCoreM <| ProofWidgets.mkRefreshComponent (.text "Loading...")
    (getStreamingResults insertPosition documentUri getter)
  displayWidget atStx html
  where
  getStreamingResults (insertPosition : Lsp.Position) (documentUri : String)
      (getter : CoreM (VerificationResults VCMetadata SmtResult × StreamingStatus)) : CoreM RefreshStep := do
    vcManager.atomicallyOnce frontendNotification (fun _ => return true) (fun _ => do IO.sleep 100; return ())
    let (results, status) ← getter
    let html := Html.ofComponent VerificationResultsViewer {results, insertPosition, documentUri} #[]
    match status with
    | .running => return .cont html
    | .done => return .last html

/-- Map VCStatus to emoji for text output. -/
def statusEmoji (status : Option VCStatus) : String :=
  match status with
  | some .proven => "✅"
  | some .disproven => "❌"
  | some .unknown => "❓"
  | some .error => "💥"
  | none => "⏳"

/-- Format a JSON value as a string, with support for nested structures. -/
private partial def formatJsonValue (json : Json) : String :=
  match json with
  | .str s => s
  | .num n => toString n
  | .bool b => toString b
  | .null => "null"
  | .arr a => s!"[{", ".intercalate (a.map formatJsonValue).toList}]"
  | .obj kvs => s!"\{{", ".intercalate (kvs.toArray.map fun (k, v) => s!"{k}: {formatJsonValue v}").toList}}"

/-- Format a JSON object as indented key-value lines. -/
private def formatJsonObject (json : Json) (indent : String := "  ") : String :=
  match json with
  | .obj kvs => "\n".intercalate (kvs.toArray.map fun (k, v) => s!"{indent}{k} = {formatJsonValue v}").toList
  | _ => formatJsonValue json

/-- Format a label JSON (action with parameters). -/
private def formatLabelJson (json : Json) : String :=
  match json with
  | .str s => s
  | .obj kvs =>
    match kvs.toArray.find? fun (_, v) => v != .null with
    | some (actionName, .obj paramKvs) =>
      s!"{actionName}({", ".intercalate (paramKvs.toArray.map fun (k, v) => s!"{k}={formatJsonValue v}").toList})"
    | some (actionName, _) => actionName
    | none => toString json
  | _ => toString json

/-- Extract counterexample JSON from a VCResult if it has one. -/
private def extractCounterexampleJson (vc : VCResult VCMetadata SmtResult) : Option Json := Id.run do
  for d in vc.timing.dischargers do
    if let some (.disproven (some (.sat counterexamples)) _) := d.result then
      for ce? in counterexamples do
        if let some ce := ce? then
          return some ce.structuredJson
  return none

/-- Format a single counterexample JSON as MessageData. -/
private def formatCounterexampleJson (json : Json) (style : String) : MessageData := Id.run do
  let theory := json.getObjValD "theory"
  let preState := json.getObjValD "preState"
  let postState := json.getObjValD "postState"
  let label := json.getObjValD "label"
  let mut msg := m!"      Counterexample ({style}):\n"
  unless theory == .null || theory == .obj {} do
    msg := msg ++ m!"        Theory:\n{formatJsonObject theory "          "}\n"
  msg := msg ++ m!"        Pre-state:\n{formatJsonObject preState "          "}\n"
  msg := msg ++ m!"        Action: {formatLabelJson label}\n"
  unless postState == .null do
    msg := msg ++ m!"        Post-state:\n{formatJsonObject postState "          "}\n"
  return msg

/-- Extract and format counterexamples from a VCResult, including TR-style alternatives. -/
private def formatCounterexamples (vc : VCResult VCMetadata SmtResult)
    (allVCs : Array (VCResult VCMetadata SmtResult)) : Option MessageData := Id.run do
  let mut msg : MessageData := m!""
  let mut hasAny := false

  -- WP-style counterexample from the primary VC
  if let some json := extractCounterexampleJson vc then
    msg := msg ++ formatCounterexampleJson json "WP"
    hasAny := true

  -- TR-style counterexample from the alternative VC (if any)
  let trVC? := allVCs.find? fun altVC => altVC.alternativeFor == some vc.id
  if let some trVC := trVC? then
    if let some json := extractCounterexampleJson trVC then
      msg := msg ++ formatCounterexampleJson json "TR"
      hasAny := true

  if hasAny then some msg else none

/-- Format verification results as text output for logging. -/
def formatVerificationResults [Monad m] [MonadOptions m](results : VerificationResults VCMetadata SmtResult) : m MessageData := do
  let includeCounterexamples := veil.printCounterexamples.get (← getOptions)
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
    if includeCounterexamples && vc.status == some .disproven then
      if let some ceMsg := formatCounterexamples vc results.vcs then
        msg := msg ++ ceMsg
  msg := msg ++ m!"The following set of actions must preserve the invariant and successfully terminate:\n"
  for (actionName, vcs) in actionGroups.toArray do
    msg := msg ++ m!"  {actionName}\n"
    for vc in vcs do
      let .induction m := vc.metadata | continue
      msg := msg ++ m!"    {m.property} ... {statusEmoji vc.status}\n"
      if includeCounterexamples && vc.status == some .disproven then
        if let some ceMsg := formatCounterexamples vc results.vcs then
          msg := msg ++ ceMsg
  return msg

/-- Check if any VCs have non-proven status. -/
def hasFailedVCs (results : VerificationResults VCMetadata SmtResult) : Bool :=
  results.vcs.any fun vc =>
    vc.metadata.isInduction && !vc.isDormant && vc.alternativeFor.isNone &&
    vc.status != some .proven

end Veil.Verifier
