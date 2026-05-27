import Veil.Core.Tools.Verifier.Server

open Lean Elab Term Command Meta

syntax (name := _root_.veil) "veil" : attr

namespace Veil.Verifier

private def veilAttrName : Name :=
  Name.mkSimple "veil"

inductive RegistrationStatus where
  | registered
  | pending
  | error (message : String)
deriving BEq

private def pushUnique (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

initialize veilTheoremExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name := `veil_theorem_ext
    addEntryFn := pushUnique
    addImportedFn := fun arrays => arrays.foldl (init := #[]) fun acc names =>
      names.foldl (init := acc) pushUnique
  }

def registeredVeilTheorems [Monad m] [MonadEnv m] : m (Array Name) := do
  return veilTheoremExt.getState (← getEnv)

-- Attribute-time registration uses `none`, allowing short names while the VC is live.
-- Replay uses `some mod.name`, so imported proofs must belong to the reopened Veil module.
private def vcNameMatches (moduleName? : Option Name) (vcName declName : Name) : Bool :=
  match moduleName? with
  | none => vcName == declName || vcName == Name.mkSimple declName.getString!
  | some moduleName => declName == moduleName ++ vcName

private def findMatchingVCs (mgr : VCManager VCMetadata SmtResult)
    (declName : Name) (moduleName? : Option Name := none) : Array VCId :=
  mgr.nodes.toArray.filterMap fun (vcId, vc) =>
    if vcNameMatches moduleName? vc.name declName then some vcId else none

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
    (declName : Name) (managerId : ManagerId) (vcId : VCId)
    (result : DischargerResult SmtResult) : BaseIO RegistrationStatus :=
  vcManager.atomically (fun ref => do
    let mgr ← ref.get
    if mgr._managerId != managerId then
      return .pending
    let some vc := mgr.nodes[vcId]?
      | return .pending
    let existingId? := findInteractiveDischargerId? vc declName
    let (discharger, result) ← mkFinishedTheoremDischarger mgr vc declName existingId? result
    let vc := match existingId? with
      | some existingId =>
        { vc with
          dischargers := vc.dischargers.set! existingId discharger
          successful := if vc.successful == some existingId && !result.isSuccessful then none else vc.successful }
      | none =>
        { vc with dischargers := vc.dischargers.push discharger }
    let mut mgr := { mgr with nodes := mgr.nodes.insert vcId vc }
    if vc.successful.isNone then
      mgr := { mgr with _doneWith := mgr._doneWith.erase vcId }
    mgr ← mgr.recordDischargerResult discharger.id result
    ref.set mgr
    return .registered)

private def currentErrorEntries (fallback : MessageData) : CoreM (Array (Exception × Json)) := do
  let msgLog ← Core.getMessageLog
  let errors := msgLog.toArray.filter (·.severity == .error)
  if errors.isEmpty then
    let text ← fallback.toString
    pure #[(Exception.error Syntax.missing fallback, Json.str text)]
  else
    errors.mapM fun msg => do
      let text ← msg.data.toString
      pure (Exception.error Syntax.missing msg.data, Json.str text)

/-- User-facing message for theorems containing `sorry`: either synthetic or explicit -/
private def theoremSorryMessage (declName : Name) (value : Expr) : MessageData :=
  if value.hasSyntheticSorry then
    m!"interactive proof `{declName}` does not discharge the goal (it has a synthetic `sorry`)"
  else
    m!"interactive proof `{declName}` contains `sorry`"

private def theoremResultForVC (declName : Name) (vc : VerificationCondition VCMetadata SmtResult) :
    CoreM (DischargerResult SmtResult) := do
  let .thmInfo info := (← getConstInfo declName)
    | throwError "`[veil]` only applies to theorems"
  if info.value.hasSorry then
    let fallback := theoremSorryMessage declName info.value
    return .error (← currentErrorEntries fallback) 0
  match ← validateTheoremWitness declName vc.toVCStatement with
  | .error ex => do
    let message ← ex.toMessageData.toString
    return .error #[(ex, Json.str message)] 0
  | .ok witness =>
    return .proven (some witness) none 0

/-- Try to register a `@[veil]` theorem against a currently live VC.
Returns `.pending` when no matching VC is live yet; the persistent attribute
entry will be retried by later verification commands. -/
def registerTheoremDischargerIfAvailable
    (declName : Name) (moduleName? : Option Name := none) : CommandElabM RegistrationStatus := do
  let mgr ← vcManager.atomically fun ref => ref.get
  let vcIds := findMatchingVCs mgr declName moduleName?
  if vcIds.size > 1 then
    return .error s!"`@[veil]` is ambiguous for `{declName}`; matched {vcIds.size} verification conditions"
  let some vcId := vcIds[0]? | return .pending
  let some vc := mgr.nodes[vcId]? | return .pending
  let result ← liftCoreM <| theoremResultForVC declName vc
  registerFinishedTheoremDischarger declName mgr._managerId vcId result

def registerAvailableTheoremDischargersFor (mod : Module) : CommandElabM Unit := do
  let mut registeredAny := false
  for declName in ← registeredVeilTheorems do
    match ← registerTheoremDischargerIfAvailable declName (some mod.name) with
    | .registered => registeredAny := true
    | .pending => pure ()
    | .error err => do
      liftM frontendNotification.notifyAll
      throwError err
  if registeredAny then
    liftM frontendNotification.notifyAll

private def registerTheoremDischargerFromAttr (declName : Name) : AttrM Unit := do
  -- `liftCommandElabM` creates a fresh command scope. Preserve the namespace
  -- where the theorem was declared so stored VC syntax can resolve local names
  -- such as `State.Label` and `send.ext` during attribute-time validation.
  let ns := (← read).currNamespace
  -- `throwOnError` propagates any command-elaborator `throwError` to the attribute caller.
  liftCommandElabM (throwOnError := true) do
    withScope (fun scope => { scope with currNamespace := ns }) do
      match ← registerTheoremDischargerIfAvailable declName with
      | .registered => liftM frontendNotification.notifyAll
      | .pending => pure ()
      | .error err => do
        liftM frontendNotification.notifyAll
        throwError err

initialize
  registerBuiltinAttribute {
    name := veilAttrName
    descr := "record a theorem as an exact discharger for a same-named verification condition"
    add := fun declName stx kind => do
      unless kind == AttributeKind.global do
        throwAttrMustBeGlobal veilAttrName kind
      let .thmInfo _info := (← getConstInfo declName)
        | throwError "`[veil]` only applies to theorems"
      modifyEnv fun env => veilTheoremExt.addEntry env declName
      registerTheoremDischargerFromAttr declName
  }

end Veil.Verifier
