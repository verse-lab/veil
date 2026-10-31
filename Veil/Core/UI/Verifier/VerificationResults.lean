module

public meta import Lean.Server.Rpc.Basic
public meta import Lean.Elab.Command
public meta import Lean.PrettyPrinter

public meta import Veil.Base
public meta import Veil.Util.ValueDisplay
public meta import ProofWidgets.Component.Basic
public meta import ProofWidgets.Component.HtmlDisplay
public meta import Veil.Core.UI.Widget.RefreshComponent
public meta import Veil.Frontend.DSL.Infra.Metadata
public meta import Veil.Core.Tools.Verifier.Results
public meta import Veil.Core.Tools.Verifier.Server

public meta section

section

namespace ProofWidgets
open Lean Server

open Veil in
structure VerificationResultsProps where
  /-- The verification results to display. -/
  results : VerificationResults VCMetadata SmtResult
  /-- Start of the outer verification command's line, for inserting theorem stubs before it. -/
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
open Veil.ValueDisplay (fields? formatJson formatText formatField formatFields formatAction)

inductive StreamingStatus where
  | running
  | done
deriving Inhabited, Server.RpcEncodable

private def displayWidget (atStx : Syntax) (html : Html) : CommandElabM Unit := do
  liftCoreM <| Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.rpcEncode html) })
    atStx

/-- Compute the theorem insertion position (start of the outer command's line) and document URI. -/
private def getTheoremInsertInfo : CommandElabM (Lsp.Position × String) := do
  let fileMap ← getFileMap
  let docUri := (← getFileName)
  -- `cmdPos` includes enclosing commands such as `set_option ... in`.
  let pos := fileMap.toPosition (← read).cmdPos
  -- FileMap positions have 1-based lines; LSP positions have 0-based lines.
  let insertPos : Lsp.Position := { line := pos.line - 1, character := 0 }
  return (insertPos, docUri)

def displayResults (atStx : Syntax) (results : VerificationResults VCMetadata SmtResult) : CommandElabM Unit := do
  let (theoremInsertPos, documentUri) ← getTheoremInsertInfo
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
  -- `FileMap.toPosition` uses 1-based lines, while LSP edits use 0-based lines.
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
  let (theoremInsertPos, documentUri) ← getTheoremInsertInfo
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

private def enumTheoryEntry? (key : String) : Option (String × String) :=
  match key.splitOn "_Enum." with
  | [enumName, ctor] =>
    if enumName.isEmpty || ctor.isEmpty then none else some (enumName, ctor)
  | _ => none

/-- Format theory entries, grouping enum adapter assignments into compact enum declarations. -/
private def formatTheoryEntries (entries : Array (String × Json)) (indent : String := "  ") :
    String :=
  let enumEntries := (entries.filterMap fun (k, _) => enumTheoryEntry? k).toList
  let regularLines := (entries.filter fun (k, _) => (enumTheoryEntry? k).isNone).toList.map
    fun (k, v) => formatField indent k v
  let enumLines := (enumEntries.map Prod.fst).eraseDups.map fun enumName =>
    let ctors := (enumEntries.filterMap fun (name, ctor) =>
      if name == enumName then some ctor else none).eraseDups
    indent ++ "enum " ++ enumName ++ " = {" ++ ", ".intercalate ctors ++ "}"
  "\n".intercalate (enumLines ++ regularLines)

/-- The theory's fields in declaration order, followed by theory-related `extraVals` such as
`tot.le` that the widget folds into the theory panel. -/
private def extractTheoryEntries (json : Json) : Array (String × Json) :=
  let theoryEntries := (fields? (json.getObjValD "theory")).getD #[]
  let extraTheoryEntries := match json.getObjValD "extraVals" with
    -- Fold any entries with dot names into the theory output, since
    -- that's how the widget treats them. These are typically instances.
    | .obj kvs => kvs.toArray.filter fun (k, _) => k.contains "."
    | _ => #[]
  theoryEntries ++ extraTheoryEntries

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
  msg := msg ++ m!"        Theory:\n{formatTheoryEntries theory "          "}\n"
  msg := msg ++ m!"        Pre-state:\n{formatFields preState "          "}\n"
  msg := msg ++ m!"{formatAction "        Action: " label}\n"
  unless postState == .null do
    msg := msg ++ m!"        Post-state:\n{formatFields postState "          "}\n"
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
  | .error exs _ => exs.map (fun (_, json) => formatText json)
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
