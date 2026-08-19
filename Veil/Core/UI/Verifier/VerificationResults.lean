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
  /-- Position after #check_invariants for inserting generated theorem stubs. -/
  theoremInsertPos : Lsp.Position
  /-- Position before #gen_spec for inserting the trust-disabling option. -/
  optionInsertPos : Option Lsp.Position
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

/-- Compute the theorem insertion position (line after the syntax) and document URI. -/
private def getTheoremInsertInfo (atStx : Syntax) : CommandElabM (Lsp.Position × String) := do
  let fileMap ← getFileMap
  let docUri := (← getFileName)
  -- Get position at end of the syntax, then move to start of next line
  let some tailPos := atStx.getTailPos? | return ({ line := 0, character := 0 }, docUri)
  let pos := fileMap.toPosition tailPos
  -- Insert at the start of the line after the command
  let insertPos : Lsp.Position := { line := pos.line, character := 0 }
  return (insertPos, docUri)

def displayResults (atStx : Syntax) (results : VerificationResults VCMetadata SmtResult) : CommandElabM Unit := do
  let (theoremInsertPos, documentUri) ← getTheoremInsertInfo atStx
  let html := Html.ofComponent VerificationResultsViewer {
    results,
    theoremInsertPos,
    optionInsertPos := none,
    documentUri
  } #[]
  displayWidget atStx html

private def getOptionInsertPos? (atStx : Syntax) : CommandElabM (Option Lsp.Position) := do
  let fileMap ← getFileMap
  let some startPos := atStx.getPos? | return none
  let pos := fileMap.toPosition startPos
  -- `FileMap.toPosition` uses 1-based lines, while LSP edits use 0-based
  -- lines. The existing tail-position insertion relies on this offset to
  -- insert after a command; inserting before a command needs the conversion.
  return some { line := pos.line - 1, character := 0 }

private partial def runStreamingResults (theoremInsertPos : Lsp.Position)
    (optionInsertPos : Option Lsp.Position) (documentUri : String)
    (getter : CoreM (VerificationResults VCMetadata SmtResult × StreamingStatus))
    (token : RefreshToken) : CoreM Unit := do
  -- CAREFUL: do not sleep while holding the lock
  IO.sleep 100
  let (results, status) ← getter
  let html := Html.ofComponent VerificationResultsViewer {
    results,
    theoremInsertPos,
    optionInsertPos,
    documentUri
  } #[]
  token.update html
  match status with
  | .running => runStreamingResults theoremInsertPos optionInsertPos documentUri getter token
  | .done => pure ()

def displayStreamingResults (atStx : Syntax)
    (getter : CoreM (VerificationResults VCMetadata SmtResult × StreamingStatus))
    (optionStx? : Option Syntax := none) : CommandElabM Unit := do
  let (theoremInsertPos, documentUri) ← getTheoremInsertInfo atStx
  let optionInsertPos ← optionStx?.mapM getOptionInsertPos? <&> Option.join
  let html ← liftCoreM <| ProofWidgets.mkRefreshComponentM (.text "Loading...")
    (runStreamingResults theoremInsertPos optionInsertPos documentUri getter)
  displayWidget atStx html

/-- Map VCStatus to emoji for text output. -/
def statusEmoji (status : Option VCStatus) : String :=
  match status with
  | some .proven => "✅"
  | some .disproven => "❌"
  | some .unknown => "❓"
  | some .error => "💥"
  | some .timeout => "⏱️"
  | none => "⏳"

/-- Resolve the user-visible status for a primary VC together with any active
TR-style alternatives. Conclusive outcomes win over sibling errors. -/
private def effectiveStatusOrder : List (Option VCStatus) :=
  [some .proven, some .disproven, none, some .error, some .timeout, some .unknown]

private def activeStatuses (vc : VCResult VCMetadata SmtResult)
    (allVCs : Array (VCResult VCMetadata SmtResult)) : Array (Option VCStatus) :=
  allVCs.foldl (init := #[vc.status]) fun acc altVC =>
    if altVC.alternativeFor == some vc.id && !altVC.isDormant then
      acc.push altVC.status
    else
      acc

private def effectiveStatus (vc : VCResult VCMetadata SmtResult)
    (allVCs : Array (VCResult VCMetadata SmtResult)) : Option VCStatus := Id.run do
  if vc.alternativeFor.isSome then
    return vc.status
  let statuses := activeStatuses vc allVCs
  return effectiveStatusOrder.find? statuses.contains |>.getD vc.status

private def isUndischargedStatus : Option VCStatus → Bool
  | some .unknown | some .error | some .timeout => true
  | some .proven | some .disproven | none => false

def undischargedTheoremTexts (results : VerificationResults VCMetadata SmtResult) :
    Array String := Id.run do
  let mut texts := #[]
  let vcs := results.vcs.qsort (·.id < ·.id)
  for vc in vcs do
    if vc.metadata.isInduction && !vc.isDormant && vc.alternativeFor.isNone &&
        isUndischargedStatus (effectiveStatus vc results.vcs) then
      if let some theoremText := vc.theoremText then
        texts := texts.push theoremText
  return texts

def undischargedTheoremStubsText (results : VerificationResults VCMetadata SmtResult) :
    Option String :=
  let texts := undischargedTheoremTexts results
  if texts.isEmpty then
    none
  else
    some ("\n\n".intercalate texts.toList)

private def formatUndischargedTheoremMessage
    (results : VerificationResults VCMetadata SmtResult) : Option MessageData :=
  let count := (undischargedTheoremTexts results).size
  if count == 0 then
    none
  else
    let conditionWord := if count == 1 then "condition" else "conditions"
    some m!"{count} verification {conditionWord} could not be discharged automatically\n"

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

private def enumTheoryEntry? (key : String) : Option (String × String) :=
  match key.splitOn "_Enum." with
  | [enumName, ctor] =>
    if enumName.isEmpty || ctor.isEmpty then none else some (enumName, ctor)
  | _ => none

/-- Format theory entries, grouping enum adapter assignments into compact enum declarations. -/
private def formatTheoryObject (json : Json) (indent : String := "  ") : String :=
  match json with
  | .obj kvs =>
    let entries := kvs.toArray
    let enumEntries := (entries.filterMap fun (k, _) => enumTheoryEntry? k).toList
    let regularLines := (entries.filter fun (k, _) => (enumTheoryEntry? k).isNone).toList.map
      fun (k, v) => s!"{indent}{k} = {formatJsonValue v}"
    let enumLines := (enumEntries.map Prod.fst).eraseDups.map fun enumName =>
      let ctors := (enumEntries.filterMap fun (name, ctor) =>
        if name == enumName then some ctor else none).eraseDups
      indent ++ "enum " ++ enumName ++ " = {" ++ ", ".intercalate ctors ++ "}"
    "\n".intercalate (enumLines ++ regularLines)
  | _ => formatJsonValue json

/-- Extract theory entries, including theory-related `extraVals` such as
`tot.le` that the widget folds into the theory panel. -/
private def extractTheoryEntries (json : Json) : Json := Id.run do
  let theoryEntries := match json.getObjValD "theory" with
    | .obj kvs => kvs.toArray
    | _ => #[]
  let extraTheoryEntries := match json.getObjValD "extraVals" with
    -- Fold any entries with dot names into the theory output, since
    -- that's how the widget treats them. These are typically instances.
    | .obj kvs => kvs.toArray.filter fun (k, _) => k.contains "."
    | _ => #[]
  Json.mkObj (theoryEntries ++ extraTheoryEntries).toList

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
  let theory := extractTheoryEntries json
  let preState := json.getObjValD "preState"
  let postState := json.getObjValD "postState"
  let label := json.getObjValD "label"
  let mut msg := m!"      Counterexample ({style}):\n"
  msg := msg ++ m!"        Theory:\n{formatTheoryObject theory "          "}\n"
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

private structure DiagnosticEntry where
  message : String
  sources : Array String
deriving Inhabited

private def addDiagnosticEntry (entries : Array DiagnosticEntry) (source message : String) :
    Array DiagnosticEntry :=
  match entries.findIdx? (·.message == message) with
  | some idx =>
    let entry := entries[idx]!
    if entry.sources.contains source then
      entries
    else
      entries.set! idx { entry with sources := entry.sources.push source }
  | none =>
    entries.push { message, sources := #[source] }

private def dischargerErrorMessages : DischargerResult SmtResult → Array String
  | .error exs _ => exs.map (fun (_, json) => formatJsonValue json)
  | .proven _ _ _ | .disproven _ _ | .unknown _ _ => #[]

private def dischargerUnknownReasons : DischargerResult SmtResult → Array String
  | .unknown (some (.unknown reasons)) _ => reasons
  | .proven _ _ _ | .disproven _ _ | .unknown _ _ | .error _ _ => #[]

private def activeRelatedVCs (vc : VCResult VCMetadata SmtResult)
    (allVCs : Array (VCResult VCMetadata SmtResult)) : Array (VCResult VCMetadata SmtResult) :=
  allVCs.foldl (init := #[vc]) fun acc altVC =>
    if altVC.alternativeFor == some vc.id && !altVC.isDormant then
      acc.push altVC
    else
      acc

private def collectDiagnostics
    (extract : DischargerResult SmtResult → Array String)
    (vc : VCResult VCMetadata SmtResult)
    (allVCs : Array (VCResult VCMetadata SmtResult)) : Array DiagnosticEntry := Id.run do
  let mut entries := #[]
  for relatedVC in activeRelatedVCs vc allVCs do
    for discharger in relatedVC.timing.dischargers do
      let source := discharger.name.toString
      for result in discharger.result.toList do
        for message in extract result do
          entries := addDiagnosticEntry entries source message
  return entries

private def indentBlock (indent text : String) : String :=
  "\n".intercalate ((text.splitOn "\n").map fun line => indent ++ line)

private def formatDiagnostics (heading : String) (entries : Array DiagnosticEntry) :
    Option MessageData := Id.run do
  if entries.isEmpty then
    return none
  let mut msg := m!"      {heading}:\n"
  for entry in entries do
    msg := msg ++ m!"        {", ".intercalate entry.sources.toList}\n"
    msg := msg ++ m!"{indentBlock "          " entry.message}\n"
  return some msg

private def formatFailureDiagnostics (status : Option VCStatus)
    (vc : VCResult VCMetadata SmtResult)
    (allVCs : Array (VCResult VCMetadata SmtResult)) : Option MessageData :=
  match status with
  | some .error | some .timeout =>
    formatDiagnostics "Exceptions" (collectDiagnostics dischargerErrorMessages vc allVCs)
  | some .unknown =>
    formatDiagnostics "Reasons for Unknown"
      (collectDiagnostics dischargerUnknownReasons vc allVCs)
  | some .proven | some .disproven | none => none

/-- Format verification results as text output for logging. -/
def formatVerificationResults [Monad m] [MonadOptions m](results : VerificationResults VCMetadata SmtResult) : m MessageData := do
  let includeCounterexamples := veil.printCounterexamples.get (← getOptions)
  let vcs := results.vcs.filter fun vc =>
    vc.metadata.isInduction && !vc.isDormant && vc.alternativeFor.isNone
  let getAction := fun vc => match vc.metadata with | .induction m => m.action | _ => .anonymous
  let initVCs := vcs.filter (getAction · == `initializer)
  let actionGroups := vcs.filter (getAction · != `initializer) |>.foldl (init := Std.HashMap.emptyWithCapacity) fun acc vc =>
    acc.insert (getAction vc) (acc.getD (getAction vc) #[] |>.push vc)

  let mut msg := m!""
  if let some theoremMsg := formatUndischargedTheoremMessage results then
    msg := msg ++ theoremMsg
  unless initVCs.isEmpty do
    msg := msg ++ m!"Initialization must establish the invariant:\n"
    for vc in initVCs do
      let .induction m := vc.metadata | continue
      let status := effectiveStatus vc results.vcs
      msg := msg ++ m!"  {m.property} ... {statusEmoji status}\n"
      if includeCounterexamples && status == some .disproven then
        if let some ceMsg := formatCounterexamples vc results.vcs then
          msg := msg ++ ceMsg
      if let some diagnosticMsg := formatFailureDiagnostics status vc results.vcs then
        msg := msg ++ diagnosticMsg
  unless actionGroups.isEmpty do
    msg := msg ++ m!"The following set of actions must preserve the invariant and successfully terminate:\n"
    for (actionName, vcs) in actionGroups.toArray do
      msg := msg ++ m!"  {actionName}\n"
      for vc in vcs do
        let .induction m := vc.metadata | continue
        let status := effectiveStatus vc results.vcs
        msg := msg ++ m!"    {m.property} ... {statusEmoji status}\n"
        if includeCounterexamples && status == some .disproven then
          if let some ceMsg := formatCounterexamples vc results.vcs then
            msg := msg ++ ceMsg
        if let some diagnosticMsg := formatFailureDiagnostics status vc results.vcs then
          msg := msg ++ diagnosticMsg
  return msg

/-- Check if any VCs have non-proven status. -/
def hasFailedVCs (results : VerificationResults VCMetadata SmtResult) : Bool :=
  results.vcs.any fun vc =>
    vc.metadata.isInduction && !vc.isDormant && vc.alternativeFor.isNone &&
    effectiveStatus vc results.vcs != some .proven

end Veil.Verifier
