module

public meta import Veil.Core.Tools.Verifier.Server

public meta section

open Lean Elab Term Meta

syntax (name := _root_.veil) "veil" : attr

namespace Veil.Verifier

private def veilAttrName : Name :=
  Name.mkSimple "veil"

/-- Sibling proof files can declare the same theorem name. Keep the defining
Lean module so reopening a spec restores only the declaration selected by Lean. -/
private structure InvariantProofEntry where
  specName : Name
  theoremName : Name
  definingModule : Name

private abbrev InvariantProofs := NameMap (Array InvariantProofEntry)

private def addProofEntry (s : InvariantProofs) (entry : InvariantProofEntry) : InvariantProofs :=
  s.insert entry.specName (((s.find? entry.specName).getD #[]).push entry)

private initialize invariantProofExt : SimplePersistentEnvExtension InvariantProofEntry InvariantProofs ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addProofEntry
    addImportedFn := mkStateFromImportedEntries addProofEntry {}
  }

private def definingModule (env : Environment) (declName : Name) : Name :=
  match env.getModuleIdxFor? declName with
  | some idx => env.header.moduleNames[idx]!
  | none => env.mainModule

private def vcNameMatches (vcName declName : Name) : Bool :=
  vcName == declName || vcName == Name.mkSimple declName.getString!

private def findMatchingVCs (mgr : VCManager VCMetadata SmtResult)
    (declName : Name) : Array VCId :=
  mgr.nodes.toArray.filterMap fun (vcId, vc) =>
    if vcNameMatches vc.name declName then some vcId else none

private def interactiveDischargerName (theoremName : Name) : Name :=
  theoremName.appendAfter "_INTERACTIVE"

private def validateTheoremWitness (declName : Name) (vcStatement : VCStatement) :
    CoreM (Except Exception Expr) := do
  try
    if (← collectAxioms declName).contains ``sorryAx then
      throwError "interactive proof `{declName}` depends on `sorry`"
    let witness ← MetaM.run' do
      let expectedType ← TermElabM.run' do
        vcStatement.type
      let witness ← instantiateMVars <| ← TermElabM.run' do
        withSynthesize (postpone := .no) $
          withoutErrToSorry $ elabTermEnsuringType (mkCIdent declName) expectedType
      if witness.hasMVar || witness.hasFVar || witness.hasSyntheticSorry then
        throwError "unsolved goals"
      pure witness
    pure (.ok witness)
  catch ex =>
    pure (.error ex)

private def mkFinishedTheoremDischarger (managerId : ManagerId)
    (vc : VerificationCondition VCMetadata SmtResult) (theoremName : Name)
    (result : DischargerResult SmtResult) : BaseIO (Discharger SmtResult) := do
  let id : DischargerIdentifier := {
    vcId := vc.uid
    -- Projection assigns the final position in the checkpoint's array.
    dischargerId := vc.dischargers.size
    name := interactiveDischargerName theoremName
    managerId := managerId
  }
  let cancelTk ← IO.CancelToken.new
  let task : SnapshotTreeTask := .pure default
  let startTimePromise ← IO.Promise.new
  startTimePromise.resolve (← IO.monoMsNow)
  let resultPromise ← IO.Promise.new
  resultPromise.resolve result
  return {
    id := id
    isInteractive := true
    term := mkIdent theoremName
    cancelTk := cancelTk
    task := some task
    startTimePromise := startTimePromise
    resultPromise := resultPromise
    mkTask := pure task
  }

/-- Commit the checked witness only while its manager generation is still current. -/
private def registerFinishedTheoremDischarger
    (owner : VCManagerEnvironment) (managerId : ManagerId) (vcId : VCId)
    (declName : Name) (result : DischargerResult SmtResult) : AttrM Unit :=
  owner.manager.atomically fun ref => do
    let mgr ← ref.get
    unless mgr._managerId == managerId do
      throwError "verification manager was reset during theorem validation"
    let some vc := mgr.nodes[vcId]?
      | throwError "`@[veil]` found verification condition {vcId}, but it is no longer registered"
    let discharger ← mkFinishedTheoremDischarger managerId vc declName result
    let registrations := (interactiveRegistrationsExt.getState (← getEnv))[managerId]?.getD #[]
    let registrations := match registrations.findIdx? (fun (d, _) =>
        d.id.vcId == vcId && d.id.name == discharger.id.name) with
      | some i => registrations.set! i (discharger, result)
      | none => registrations.push (discharger, result)
    modifyEnv fun env => interactiveRegistrationsExt.modifyState env (·.insert managerId registrations)

private def currentErrorEntries (fallback : MessageData) : AttrM (Array (Exception × Json)) := do
  let msgLog ← Core.getMessageLog
  let errors := msgLog.toArray.filter (·.severity == .error)
  if errors.isEmpty then
    let text ← fallback.toString
    pure #[(Exception.error Syntax.missing fallback, Json.str text)]
  else
    errors.mapM fun msg => do
      let text ← msg.data.toString
      pure (Exception.error Syntax.missing msg.data, Json.str text)

private def registerTheoremDischarger (declName : Name) (errors : Array (Exception × Json) := #[]) :
    AttrM VCMetadata := do
  let owner ← getVCManagerOwner
  let mgr ← owner.manager.atomically fun ref => ref.get
  let ids := findMatchingVCs mgr declName
  let #[vcId] := ids
    | if ids.isEmpty then
        throwError "`@[veil]` could not find a verification condition named `{declName}`"
      else
        throwError "`@[veil]` is ambiguous for `{declName}`; matched {ids.size} verification conditions"
  let vc := mgr.nodes[vcId]!
  let result ← if !errors.isEmpty then pure (.error errors 0) else do
    match ← validateTheoremWitness declName vc.toVCStatement with
    | .error ex => pure (.error #[(ex, Json.str (← ex.toMessageData.toString))] 0)
    | .ok witness => pure (.proven (some witness) none 0)
  registerFinishedTheoremDischarger owner mgr._managerId vcId declName result
  return vc.metadata

/-- User-facing message for theorems containing `sorry`: either synthetic or explicit -/
private def theoremSorryMessage (declName : Name) (value : Expr) : MessageData :=
  if value.hasSyntheticSorry then
    m!"interactive proof `{declName}` does not discharge the goal (it has a synthetic `sorry`)"
  else
    m!"interactive proof `{declName}` contains `sorry`"

/-- Recheck each selected declaration against the reopened spec. Lean's exported
axiom dependencies are available even when the theorem body is hidden. -/
def restoreInvariantProofs (specName : Name) : CoreM Unit := do
  let env ← getEnv
  let some entries := (invariantProofExt.getState env).find? specName | return
  for entry in entries do
    if entry.definingModule == definingModule env entry.theoremName then
      discard <| registerTheoremDischarger entry.theoremName

initialize
  registerBuiltinAttribute {
    name := veilAttrName
    descr := "register a theorem as an exact discharger for the verification condition with the same name"
    add := fun declName stx kind => do
      unless kind == AttributeKind.global do
        throwAttrMustBeGlobal veilAttrName kind
      let .thmInfo info ← withoutExporting <| getConstInfo declName
        | throwError "`[veil]` only applies to theorems"
      let errors ← if info.value.hasSorry then
          currentErrorEntries (theoremSorryMessage declName info.value)
        else pure #[]
      let metadata ← registerTheoremDischarger declName errors
      if metadata.isInduction && !isPrivateName declName then
        let some mod := (← localEnv.get).currentModule | return
        let entry : InvariantProofEntry := {
          specName := mod.name
          theoremName := declName
          definingModule := definingModule (← getEnv) declName
        }
        modifyEnv (invariantProofExt.addEntry · entry)
  }

end Veil.Verifier
