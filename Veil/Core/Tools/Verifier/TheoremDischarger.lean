module

meta import Veil.Core.Tools.Verifier.Server

public meta section

open Lean Elab Term Meta

syntax (name := _root_.veil) "veil" : attr

namespace Veil.Verifier

private def veilAttrName : Name :=
  Name.mkSimple "veil"

private def vcNameMatches (vcName declName : Name) : Bool :=
  vcName == declName || vcName == Name.mkSimple declName.getString!

private def findMatchingVCs (mgr : VCManager VCMetadata SmtResult)
    (declName : Name) : Array VCId :=
  mgr.nodes.toArray.filterMap fun (vcId, vc) =>
    if vcNameMatches vc.name declName then some vcId else none

private def interactiveDischargerName (theoremName : Name) : Name :=
  Name.mkSimple s!"{theoremName.getString!}_INTERACTIVE"

private def findInteractiveDischargerId? (vc : VerificationCondition VCMetadata SmtResult)
    (theoremName : Name) : Option DischargerId :=
  let interactiveName := interactiveDischargerName theoremName
  vc.dischargers.findIdx? fun discharger =>
    discharger.isInteractive && discharger.id.name == interactiveName

private def validateTheoremWitness (declName : Name) (vcStatement : VCStatement) :
    CoreM (Except Exception Expr) := do
  try
    let witness ← MetaM.run' do
      let expectedType ← TermElabM.run' do
        vcStatement.type
      let witness ← instantiateMVars <| ← TermElabM.run' do
        withSynthesize (postpone := .no) $
          withoutErrToSorry $ elabTermEnsuringType (mkIdent declName) expectedType
      if witness.hasMVar || witness.hasFVar || witness.hasSyntheticSorry then
        throwError "unsolved goals"
      pure witness
    pure (.ok witness)
  catch ex =>
    pure (.error ex)

private def mkFinishedTheoremDischarger (mgr : VCManager VCMetadata SmtResult)
    (vc : VerificationCondition VCMetadata SmtResult) (theoremName : Name)
    (existingId? : Option DischargerId := none)
    (result : DischargerResult SmtResult) :
    BaseIO (Discharger SmtResult × DischargerResult SmtResult) := do
  let dischargerId := existingId?.getD vc.dischargers.size
  let id : DischargerIdentifier := {
    vcId := vc.uid
    dischargerId := dischargerId
    name := interactiveDischargerName theoremName
    managerId := mgr._managerId
  }
  let cancelTk ← IO.CancelToken.new
  let task ← BaseIO.asTask (pure (default : Lean.Language.SnapshotTree)) (prio := .dedicated)
  let startTimePromise ← IO.Promise.new
  startTimePromise.resolve (← IO.monoMsNow)
  let resultPromise ← IO.Promise.new
  resultPromise.resolve result
  let discharger : Discharger SmtResult := {
    id := id
    isInteractive := true
    term := mkIdent theoremName
    cancelTk := cancelTk
    task := some task
    startTimePromise := startTimePromise
    resultPromise := resultPromise
    mkTask := pure task
  }
  pure (discharger, result)

private def registerFinishedTheoremDischarger
    (owner : VCManagerEnvironment) (managerId : ManagerId)
    (declName : Name) (result : DischargerResult SmtResult) : AttrM (Except String Unit) := do
  -- Recheck the captured owner generation after validation, and commit the
  -- immutable registration while holding its lock. A reset cannot interleave.
  let res ← owner.manager.atomically fun ref => do
    let mgr ← ref.get
    if mgr._managerId != managerId then
      return Except.error "verification manager was reset during theorem validation"
    let registrations := (interactiveRegistrationsExt.getState (← getEnv))[managerId]?.getD #[]
    let view ← mgr.withInteractiveResults registrations
    let vcIds := findMatchingVCs view declName
    if vcIds.isEmpty then
      return Except.error s!"`@[veil]` could not find a verification condition named `{declName}`"
    else if vcIds.size = 1 then
      let vcId := vcIds[0]!
      let some vc := view.nodes[vcId]?
        | return Except.error s!"`@[veil]` found verification condition {vcId}, but it is no longer registered"
      let existingId? := findInteractiveDischargerId? vc declName
      let (discharger, result) ← mkFinishedTheoremDischarger view vc declName existingId? result
      let registrations := match registrations.findIdx? (fun (d, _) =>
          d.id.vcId == discharger.id.vcId && d.id.name == discharger.id.name) with
        | some i => registrations.set! i (discharger, result)
        | none => registrations.push (discharger, result)
      modifyEnv fun env => interactiveRegistrationsExt.modifyState env (·.insert managerId registrations)
      return Except.ok ()
    else
      return Except.error s!"`@[veil]` is ambiguous for `{declName}`; matched {vcIds.size} verification conditions"
  return res

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

private def registerTheoremDischarger (declName : Name) : AttrM Unit := do
  let res ← do
    let owner ← getVCManagerOwner
    let mgr ← owner.manager.atomically fun ref => ref.get
    let vcIds := findMatchingVCs mgr declName
    if vcIds.isEmpty then
      pure <| Except.error s!"`@[veil]` could not find a verification condition named `{declName}`"
    else if vcIds.size = 1 then
      let vcId := vcIds[0]!
      let some vc := mgr.nodes[vcId]?
        | pure <| Except.error s!"`@[veil]` found verification condition {vcId}, but it is no longer registered"
      let witnessResult ← validateTheoremWitness declName vc.toVCStatement
      match witnessResult with
      | .error ex => do
        let message ← ex.toMessageData.toString
        let result : DischargerResult SmtResult :=
          .error #[(ex, Json.str message)] 0
        registerFinishedTheoremDischarger owner mgr._managerId declName result
      | .ok witness => do
        let result : DischargerResult SmtResult :=
          .proven (some witness) none 0
        registerFinishedTheoremDischarger owner mgr._managerId declName result
    else
      pure <| Except.error s!"`@[veil]` is ambiguous for `{declName}`; matched {vcIds.size} verification conditions"
  match res with
  | .ok () => liftM frontendNotification.notifyAll
  | .error err => do
    liftM frontendNotification.notifyAll
    throwError err

/-- User-facing message for theorems containing `sorry`: either synthetic or explicit -/
private def theoremSorryMessage (declName : Name) (value : Expr) : MessageData :=
  if value.hasSyntheticSorry then
    m!"interactive proof `{declName}` does not discharge the goal (it has a synthetic `sorry`)"
  else
    m!"interactive proof `{declName}` contains `sorry`"

initialize
  registerBuiltinAttribute {
    name := veilAttrName
    descr := "register a theorem as an exact discharger for the verification condition with the same name"
    add := fun declName stx kind => do
      unless kind == AttributeKind.global do
        throwAttrMustBeGlobal veilAttrName kind
      -- Public theorems are exported as axioms; inspect the local proof to
      -- retain the checks for unfinished interactive proofs.
      let .thmInfo info ← withoutExporting <| getConstInfo declName
        | throwError "`[veil]` only applies to theorems"
      if info.value.hasSorry then
        let fallback := theoremSorryMessage declName info.value
        let result : DischargerResult SmtResult := .error (← currentErrorEntries fallback) 0
        let owner ← getVCManagerOwner
        let mgr ← owner.manager.atomically fun ref => ref.get
        let res ← registerFinishedTheoremDischarger owner mgr._managerId declName result
        match res with
        | .ok () => liftM frontendNotification.notifyAll
        | .error err => throwError err
        return
      registerTheoremDischarger declName
  }

end Veil.Verifier
