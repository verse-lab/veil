import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Util
import Veil.Core.Tools.Verifier.Manager
import Veil.Core.Tools.Verifier.Results
import Std.Sync.Mutex
import Veil.Util.Multiprocessing
import Veil.Util.Meta

namespace Veil.Verifier

open Lean Elab Command Term Std

-- FIXME: this should be in `EnvExtensions.lean`, but putting it there triggers
-- the bug fixed in [#10217](https://github.com/leanprover/lean4/pull/10217).
-- Placing it here as a workaround until the fix ships in a stable Lean.
/-- Holds the state of the VCManager for the current file. -/
initialize vcManager : Std.Mutex (VCManager VCMetadata SmtResult) ← Std.Mutex.new (← VCManager.new vcManagerCh)

def sendNotification (notification : ManagerNotification VCMetadata SmtResult) : CommandElabM Unit := do
  let _ ← vcManagerCh.send notification

/-- Run a computation with exclusive access to the VCManager.
    Use this for batching multiple VC operations atomically. -/
def withVCManager (f : IO.Ref (VCManager VCMetadata SmtResult) → CommandElabM α) : CommandElabM α :=
  vcManager.atomically f

def reset (managerId : ManagerId) : CommandElabM Unit := sendNotification (.reset managerId)
def startAll : CommandElabM Unit := sendNotification .startAll
def startFiltered (filter : VCMetadata → Bool) : CommandElabM Unit := sendNotification (.startFiltered filter)

def isDoesNotThrow (m : VCMetadata) : Bool := m.propertyName? == some `doesNotThrow

/-- Start the given dischargers, send them to the task registration channel for the frontend
    to register via `logSnapshotTask`, and update the VCManager with the started tasks. -/
private def startAndRegisterTasks
    (toStart : Array (VerificationCondition VCMetadata SmtResult × Discharger SmtResult))
    : CommandElabM Unit := do
  for (vc, discharger) in toStart do
    let discharger' ← discharger.run
    if let some task := discharger'.task then
      -- Send to channel for frontend to register (instead of registering directly here)
      let _ ← Veil.taskRegistrationCh.send { task, cancelTk := discharger'.cancelTk }
    vcManager.atomically (fun ref => do
      let mut mgr ← ref.get
      let vc' := { vc with dischargers := vc.dischargers.set! discharger.id.dischargerId discharger' }
      mgr := { mgr with nodes := mgr.nodes.insert vc.uid vc' }
      ref.set mgr)
  -- Notify frontend that new tasks are available to register
  Frontend.notify

/-- Starts a separate task (on a dedicated thread) that runs the VCManager.
If this is called multiple times, each call will reset the VC manager. -/
def runManager (cancelTk? : Option IO.CancelToken := none) : CommandElabM Unit := do
  let cancelTk := cancelTk?.getD (← IO.CancelToken.new)
  let managerLoop ← Command.wrapAsyncAsSnapshot (fun () => do
    -- dbg_trace "({← IO.monoMsNow}) [Manager] Starting manager loop"
    while true do
      try
        -- blocks until we get a notification
        -- NOTE: this `get` is really problematic, as it increases the threadpool size
        let notification := (← vcManagerCh.recv).get
        match notification with
        | .dischargerResult dischargerId res => do
          -- Phase 1: Update state, get ready tasks (inside atomically)
          let toStart ← vcManager.atomically (fun ref => do
            let mut mgr ← ref.get
            if dischargerId.managerId != mgr._managerId then
              -- dbg_trace "({← IO.monoMsNow}) [Manager] RECV dischargerResult from manager ID {dischargerId.managerId} (our ID: {mgr._managerId}); ignoring"
              return #[]
            -- dbg_trace "({← IO.monoMsNow}) [Manager] RECV {res.kindString} notification from discharger {dischargerId} after {res.time}ms (solved: {mgr._totalSolved}/{mgr.nodes.size})"
            mgr ← mgr.recordDischargerResult dischargerId res
            -- Get ready tasks AFTER markDischarger so freshly woken alternatives can be scheduled
            let ready ← mgr.readyTasks
            let ready := ready.take 1  -- Only start 1 at a time
            ref.set mgr
            return ready.toArray)
          -- Phase 2 & 3: Start tasks, register snapshots, and update manager
          startAndRegisterTasks toStart
          Frontend.notify
          -- dbg_trace "({← IO.monoMsNow}) [Manager] SEND frontend notification"
        | .startAll => do
          -- Phase 1: Get ready tasks (inside atomically)
          let toStart ← vcManager.atomically (fun ref => do
            let mgr ← ref.get
            -- dbg_trace "({← IO.monoMsNow}) [Manager] RECV startAll notification"
            let ready ← mgr.readyTasks
            let ready := ready.take (← getNumCores)
            return ready.toArray)
          -- Phase 2 & 3: Start tasks, register snapshots, and update manager
          startAndRegisterTasks toStart
        | .startFiltered filter => do
          -- Phase 1: Get ready tasks matching filter (inside atomically)
          let toStart ← vcManager.atomically (fun ref => do
            let mgr ← ref.get
            -- let _matches := mgr.nodes.values.filter (fun node => filter node.metadata) |>.map (·.metadata.displayName)
            -- dbg_trace "({← IO.monoMsNow}) [Manager] RECV startFiltered notification (matches: {_matches})"
            let ready ← mgr.readyTasks filter
            let ready := ready.take (← getNumCores)
            return ready.toArray)
          -- Phase 2 & 3: Start tasks, register snapshots, and update manager
          startAndRegisterTasks toStart
          -- Check if done and notify
          vcManager.atomically (fun ref => do
            let mgr ← ref.get
            if mgr.isDoneFiltered filter then Frontend.notify)
        | .reset managerId => vcManager.atomically (fun ref => do
          let mut mgr ← ref.get
          if mgr._managerId != managerId then
            -- dbg_trace "({← IO.monoMsNow}) [Manager] RECV reset notification for manager ID {managerId} (our ID: {mgr._managerId}); ignoring"
            return
          -- dbg_trace "({← IO.monoMsNow}) [Manager] RECV reset notification meant for us (manager ID: {mgr._managerId})"
          mgr ← VCManager.new vcManagerCh (currentManagerId := mgr._managerId)
          ref.set mgr)
      catch ex =>
        -- Log errors but continue processing to prevent the manager loop from dying
        dbg_trace "[VCManager] Error in manager loop: {← ex.toMessageData.toString}"
  ) cancelTk
  vcServerStarted.atomically (fun ref => do
    if !(← ref.get) then
      -- Start the manager task but DON'T register with logSnapshotTask.
      -- The manager loop is infinite, so registering it would hang the build.
      -- Discharger tasks are registered by runFilteredAsync/waitFilteredSync instead.
      -- dbg_trace "({← IO.monoMsNow}) [Manager] Starting manager loop"
      let _ ← (managerLoop ()).asTask
    else
      vcManager.atomically (fun managerRef => do
        let mgr ← managerRef.get
        let mgr ← VCManager.new vcManagerCh (currentManagerId := mgr._managerId)
        managerRef.set mgr
        -- dbg_trace "({← IO.monoMsNow}) [Manager] Reset state for manager ID {mgr._managerId}"
        )
    ref.set true
  )

/-- Log any pending discharger tasks from the channel via `logSnapshotTask` (non-blocking). -/
private partial def logPendingDischargerTasks : CommandElabM Unit := do
  if let some info ← Veil.taskRegistrationCh.tryRecv then
    Command.logSnapshotTask { stx? := none, cancelTk? := info.cancelTk, task := info.task }
    logPendingDischargerTasks

/-- Poll for discharger tasks from the manager and register them with `logSnapshotTask`.
    Waits until all VCs matching the filter are done, then returns the results.
    This enables profiler trace propagation by registering tasks on the calling thread. -/
private def awaitFilteredWithLogging (filter : VCMetadata → Bool)
    : CommandElabM (VerificationResults VCMetadata SmtResult) := do
  while true do
    logPendingDischargerTasks
    let result? ← vcManager.atomically fun ref => do
      let mgr ← ref.get
      if mgr.isDoneFiltered filter then
        return some (← liftCoreM (mgr.toResults filter))
      else
        return none
    if let some results := result? then return results
    IO.sleep 10
  panic! "unreachable"

/-- Start VCs matching the filter and run the callback asynchronously when done.
Uses `wrapAsyncAsSnapshot` so that errors from the callback are reported to the user.
This task also polls for discharger tasks from the manager and registers them with
`logSnapshotTask`, enabling profiler trace propagation.
Note: Widget display does not work in the callback since it runs in an async context. -/
def runFilteredAsync (filter : VCMetadata → Bool)
    (callback : VerificationResults VCMetadata SmtResult → CommandElabM Unit) : CommandElabM Unit := do
  startFiltered filter
  let cancelTk ← IO.CancelToken.new
  let wrappedTask ← Command.wrapAsyncAsSnapshot (fun () => do
    let results ← awaitFilteredWithLogging filter
    callback results) cancelTk
  let task ← (wrappedTask ()).asTask
  Command.logSnapshotTask { stx? := none, cancelTk? := cancelTk, task := task }

/-- Start VCs matching the filter and wait synchronously for completion.
Returns the results on the main thread, allowing widget display.
This also polls for discharger tasks from the manager and registers them with
`logSnapshotTask`, enabling profiler trace propagation.
Warning: This blocks the elaborator until all matching VCs complete. -/
def waitFilteredSync (filter : VCMetadata → Bool) : CommandElabM (VerificationResults VCMetadata SmtResult) := do
  startFiltered filter
  awaitFilteredWithLogging filter

inductive GenTheoremsPhase where
  | waitingForVCs
  | generatingTheorems
  | done
deriving Inhabited, BEq

inductive GenTheoremsDeclStatus where
  | pending
  | existing
  | generated
  | failed
deriving Inhabited, BEq

structure GenTheoremsDeclProgress where
  name : Name
  style : VCStyle
  status : GenTheoremsDeclStatus := .pending
deriving Inhabited

structure GenTheoremsProgress where
  phase : GenTheoremsPhase := .waitingForVCs
  total : Nat := 0
  omitted : Nat := 0
  existing : Nat := 0
  reserved : Nat := 0
  generated : Nat := 0
  failed : Nat := 0
  decls : Array GenTheoremsDeclProgress := #[]
  failures : Array String := #[]
  startTimeMs : Nat := 0
deriving Inhabited

abbrev GenTheoremsProgressRef := IO.Ref GenTheoremsProgress

def GenTheoremsProgress.isDone (p : GenTheoremsProgress) : Bool :=
  p.phase == .done

private def ensureExistingTheoremMatches (fullName : Name) (statement : Expr) : TermElabM Unit := do
  let some info := (← getEnv).findConstVal? fullName
    | return
  unless ← Meta.isDefEq info.type statement do
    throwError "cannot generate VC theorem `{fullName}` because a declaration with that name already exists with a different type"

private def vcTheoremFullName (vc : VerificationCondition VCMetadata SmtResult) : TermElabM Name := do
  return (← getCurrNamespace).append vc.name

private def vcTheoremAvailable (vc : VerificationCondition VCMetadata SmtResult) : TermElabM Bool := do
  let fullName ← vcTheoremFullName vc
  let some info := (← getEnv).findConstVal? fullName
    | return false
  Meta.isDefEq info.type (← vc.toVCStatement.type)

private structure ReservedVCTheorem where
  vcId : VCId
  vc : VerificationCondition VCMetadata SmtResult
  fullName : Name
  statement : Expr
  async : Environment.AddConstAsyncResult

private inductive VCTheoremReservation where
  | existing (fullName : Name)
  | reserved (entry : ReservedVCTheorem)

private inductive GenTheoremAttempt where
  | pending
  | generated
  | failed

private def addDeclCoreChecked (decl : Declaration) : CoreM Unit := do
  let opts ← getOptions
  let env ← (← getEnv).addDeclCore (Core.getMaxHeartbeats opts).toUSize decl
    (← read).cancelTk? (!debug.skipKernelTC.get opts)
    |> ofExceptKernelException
  setEnv env

private def addDeclAsAxiomFallback (decl : Declaration) : CoreM Unit := do
  let tryAdd (decl : Declaration) : CoreM Bool := do
    try
      addDeclCoreChecked decl
      return true
    catch _ =>
      return false
  match decl with
  | .defnDecl d | .thmDecl d =>
    if ← tryAdd <| .axiomDecl {
        name := d.name
        levelParams := d.levelParams
        type := d.type
        isUnsafe := false } then
      return
  | _ => pure ()
  for n in decl.getNames do
    if ← tryAdd <| .axiomDecl {
        name := n
        levelParams := []
        type := mkApp2 (mkConst ``sorryAx [1]) (mkSort 0) (mkConst ``true)
        isUnsafe := false } then
      return

private def checkDeclOrFallback (decl : Declaration) : CoreM Unit := do
  try
    profileitM Exception "type checking" (← getOptions) do
      withTraceNode `Kernel (fun _ => return m!"typechecking declarations {decl.getTopLevelNames}") do
        warnIfUsesSorry decl
        addDeclCoreChecked decl
  catch ex =>
    addDeclAsAxiomFallback decl
    throw ex

private def exportedTheoremInfo (env : Environment) (thm : TheoremVal) : ConstantInfo :=
  if env.header.isModule then
    .axiomInfo { thm with isUnsafe := false }
  else
    .thmInfo thm

private def exportedTheoremKind (env : Environment) : ConstantKind :=
  if env.header.isModule then .axiom else .thm

private def sorryProof (statement : Expr) : Expr :=
  mkApp2 (mkConst ``sorryAx [0]) statement (mkConst ``true)

private def addVCTheoremDeclAsync (vcName fullName : Name)
    (statement proof : Expr) : TermElabM Unit := do
  withTraceNode (`veil.perf.definition ++ vcName) (fun _ => return s!"thm {vcName}") do
    let thm := mkTheoremValEx fullName [] statement proof []
    let decl := Declaration.thmDecl thm
    let info := ConstantInfo.thmInfo thm
    let exportedInfo := exportedTheoremInfo (← getEnv) thm
    let async ← (← getEnv).addConstAsync fullName .thm
      (exportedKind? := some (.ofConstantInfo exportedInfo))
    async.commitConst async.asyncEnv (some info) (some exportedInfo)
    setEnv async.mainEnv
    enableRealizationsForConst fullName
    let cancelTk ← IO.CancelToken.new
    let checkAct ← Core.wrapAsyncAsSnapshot (cancelTk? := cancelTk)
        (desc := s!"typechecking theorem {fullName}") fun _ => do
      setEnv async.asyncEnv
      try
        checkDeclOrFallback decl
      finally
        async.commitCheckEnv (← getEnv)
    Core.logSnapshotTask {
      stx? := none
      reportingRange := .skip
      task := (← BaseIO.asTask (checkAct ()))
      cancelTk? := cancelTk }

private def reserveVCTheorem (vcId : VCId) (vc : VerificationCondition VCMetadata SmtResult) :
    TermElabM VCTheoremReservation := do
  let fullName ← vcTheoremFullName vc
  let statement ← vc.toVCStatement.type
  if (← getEnv).contains fullName then
    ensureExistingTheoremMatches fullName statement
    return .existing fullName
  let env ← getEnv
  let async ← env.addConstAsync fullName .thm (exportedKind? := some (exportedTheoremKind env))
  let sig : ConstantVal := { name := fullName, levelParams := [], type := statement }
  async.commitSignature sig
  setEnv async.mainEnv
  enableRealizationsForConst fullName
  return .reserved { vcId, vc, fullName, statement, async }

private def commitReservedVCTheorem (reserved : ReservedVCTheorem) (proof : Expr) :
    TermElabM Unit := do
  withTraceNode (`veil.perf.definition ++ reserved.vc.name)
      (fun _ => return s!"thm {reserved.vc.name}") do
    setEnv reserved.async.asyncEnv
    let proof ← instantiateMVars proof
    let thm := mkTheoremValEx reserved.fullName [] reserved.statement proof []
    let decl := Declaration.thmDecl thm
    let info := ConstantInfo.thmInfo thm
    let exportedInfo := exportedTheoremInfo (← getEnv) thm
    reserved.async.commitConst reserved.async.asyncEnv (some info) (some exportedInfo)
    let cancelTk ← IO.CancelToken.new
    let checkAct ← Core.wrapAsyncAsSnapshot (cancelTk? := cancelTk)
        (desc := s!"typechecking theorem {reserved.fullName}") fun _ => do
      setEnv reserved.async.asyncEnv
      try
        checkDeclOrFallback decl
      finally
        reserved.async.commitCheckEnv (← getEnv)
    Core.logSnapshotTask {
      stx? := none
      reportingRange := .skip
      task := (← BaseIO.asTask (checkAct ()))
      cancelTk? := cancelTk }

/-- Add a theorem declaration for a VC using the provided proof witness.
Existing declarations with the same type are accepted to keep `#gen_theorems`
idempotent; existing declarations with another type are rejected. -/
def addVCTheorem (vc : VerificationCondition VCMetadata SmtResult)
    (witness : Witness) : CommandElabM Unit := do
  liftTermElabM do
    let fullName ← vcTheoremFullName vc
    let statement ← vc.toVCStatement.type
    if (← getEnv).contains fullName then
      ensureExistingTheoremMatches fullName statement
      return
    let witness ← instantiateMVars witness
    addVCTheoremDeclAsync vc.name fullName statement witness
    return ()

private def inductionMetadata? (vc : VerificationCondition VCMetadata SmtResult) :
    Option InductionVCMetadata :=
  match vc.metadata with
  | .induction m => some m
  | .trace _ => none

private def isBridgeableInductionPair (source target : VerificationCondition VCMetadata SmtResult) :
    Bool :=
  match inductionMetadata? source, inductionMetadata? target with
  | some sourceMeta, some targetMeta =>
    sourceMeta.action == targetMeta.action &&
      sourceMeta.property == targetMeta.property &&
      ((sourceMeta.style == .wp && targetMeta.style == .tr) ||
        (sourceMeta.style == .tr && targetMeta.style == .wp))
  | _, _ => false

private def derivedTransitionEqFullName? (actName : Name) : TermElabM (Option Name) := do
  let fullName := (← getCurrNamespace).append (toDerivedEqName (toExtName actName))
  if (← getEnv).contains fullName then
    return some fullName
  else
    return none

private def mkEquivalentInductionWitnessFromProof
    (source target : VerificationCondition VCMetadata SmtResult) (sourceWitness : Witness) :
    TermElabM (Option Witness) := do
  let some sourceMeta := inductionMetadata? source | return none
  let some targetMeta := inductionMetadata? target | return none
  unless isBridgeableInductionPair source target do
    return none
  let some derivedEqName ← derivedTransitionEqFullName? sourceMeta.action
    | return none
  let derivedEqIdent := mkIdent derivedEqName
  let assumingEqIdent := mkIdent (`Veil ++ `Transition ++ `meetsSpecificationIfSuccessfulAssuming_eq)
  let soundIdent := mkIdent (`Veil ++ `VeilM ++ `toTransitionDerived_sound)
  let sourceStatement ← source.toVCStatement.type
  let targetStatement ← target.toVCStatement.type
  let env0 ← getEnv
  let (witness, envWithFreshProofs) ← withoutModifyingEnv' do
    setEnv env0.unlockAsync
    Meta.withLocalDeclD `sourceProof sourceStatement fun sourceProof => do
      let sourceIdent := mkIdent `sourceProof
      let proofStx? ← match sourceMeta.style, targetMeta.style with
        | .wp, .tr =>
          some <$> `(term| by
            simpa [← $assumingEqIdent:ident, $soundIdent:ident, $derivedEqIdent:ident] using $sourceIdent:ident)
        | .tr, .wp =>
          some <$> `(term| by
            simpa [$assumingEqIdent:ident, ← $soundIdent:ident, ← $derivedEqIdent:ident] using $sourceIdent:ident)
        | _, _ => pure none
      let some proofStx := proofStx?
        | return sourceProof
      let proof ← instantiateMVars <| ← withSynthesize (postpone := .no) <|
        withoutErrToSorry $ elabTermEnsuringType proofStx targetStatement
      let proofFn ← Meta.mkLambdaFVars #[sourceProof] proof
      return mkApp proofFn sourceWitness
  let witness ← withEnv envWithFreshProofs <| inlineFreshProofs env0 witness (rec := true)
  let witness ← instantiateMVars witness
  if witness.hasMVar || witness.hasFVar || witness.hasSyntheticSorry then
    throwError "failed to generate equivalent VC theorem `{target.name}` from `{source.name}`"
  return some witness

private def mkEquivalentInductionWitness (source target : VerificationCondition VCMetadata SmtResult) :
    TermElabM (Option Witness) := do
  let sourceName ← vcTheoremFullName source
  mkEquivalentInductionWitnessFromProof source target (mkConst sourceName)

private def addEquivalentTheoremIfAvailable (source target : VerificationCondition VCMetadata SmtResult) :
    CommandElabM Unit := do
  let sourceAvailable ← liftTermElabM <| vcTheoremAvailable source
  unless sourceAvailable do
    return
  let targetAvailable ← liftTermElabM <| vcTheoremAvailable target
  if targetAvailable then
    return
  match ← liftTermElabM <| mkEquivalentInductionWitness source target with
  | some witness => addVCTheorem target witness
  | none => return

/-- Add theorem declarations for all already-proven VCs matching `filter`.

This must run on the command elaboration thread, not in the manager task: it
mutates the current Lean environment by adding theorem constants whose proofs
are the witnesses returned by successful dischargers. Declarations are added in
the manager DAG's dependency order so downstream proof terms can refer to
upstream VC theorem constants. -/
def addProvenTheoremsInDependencyOrder (filter : VCMetadata → Bool) : CommandElabM Unit := do
  let mgr ← vcManager.atomically fun ref => ref.get
  for vcId in mgr.vcIdsInDependencyOrder filter do
    if let some (vc, witness) := mgr.provenWitness? vcId then
      addVCTheorem vc witness

/-- Add theorem declarations for dormant WP/TR alternatives whose paired VC has
already been materialized as a theorem. These proof terms use the generated
semantic equivalence theorems and do not affect VC scheduling or SMT state. -/
def addEquivalentInductionTheoremsInDependencyOrder (filter : VCMetadata → Bool) : CommandElabM Unit := do
  let mgr ← vcManager.atomically fun ref => ref.get
  for primaryId in mgr.vcIdsInDependencyOrder filter do
    let some primaryVC := mgr.nodes[primaryId]?
      | continue
    let some altIds := mgr.alternativeVCs[primaryId]?
      | continue
    for altId in altIds do
      let some altVC := mgr.nodes[altId]?
        | continue
      unless filter primaryVC.metadata && filter altVC.metadata do
        continue
      unless isBridgeableInductionPair primaryVC altVC do
        continue
      addEquivalentTheoremIfAvailable primaryVC altVC
      addEquivalentTheoremIfAvailable altVC primaryVC

private def collectGenTheoremCandidates (filter : VCMetadata → Bool) :
    CommandElabM (Array (VCId × VerificationCondition VCMetadata SmtResult)) := do
  let mgr ← vcManager.atomically fun ref => ref.get
  return (mgr.vcIdsInDependencyOrder filter).filterMap fun vcId => do
    let vc ← mgr.nodes[vcId]?
    some (vcId, vc)

private def vcHasDirectGenSource (mgr : VCManager VCMetadata SmtResult) (vcId : VCId) :
    Bool :=
  match mgr.nodes[vcId]? with
  | none => false
  | some vc => (mgr.provenWitness? vcId).isSome || !vc.effectiveDischargers.isEmpty

private def alternativePeerIds (mgr : VCManager VCMetadata SmtResult) (targetId : VCId) :
    Array VCId := Id.run do
  let mut peers := #[]
  for (primaryId, altIds) in mgr.alternativeVCs.toArray do
    if primaryId == targetId then
      peers := peers ++ altIds
    else if altIds.contains targetId then
      peers := peers.push primaryId
  return peers

private def existingVCTheoremFullName? (vc : VerificationCondition VCMetadata SmtResult) :
    TermElabM (Option Name) := do
  let fullName ← vcTheoremFullName vc
  let statement ← vc.toVCStatement.type
  if (← getEnv).contains fullName then
    ensureExistingTheoremMatches fullName statement
    return some fullName
  return none

private def filterGeneratableTheoremCandidates
    (candidates : Array (VCId × VerificationCondition VCMetadata SmtResult)) :
    CommandElabM (Array (VCId × VerificationCondition VCMetadata SmtResult) × Nat) := do
  let mgr ← vcManager.atomically fun ref => ref.get
  let existingIds ← liftTermElabM do
    let mut existingIds : Std.HashSet VCId := Std.HashSet.emptyWithCapacity
    for (vcId, vc) in candidates do
      if (← existingVCTheoremFullName? vc).isSome then
        existingIds := existingIds.insert vcId
    return existingIds
  let mut sourceIds : Std.HashSet VCId := existingIds
  for (vcId, _) in candidates do
    if vcHasDirectGenSource mgr vcId then
      sourceIds := sourceIds.insert vcId
  let mut eligible := #[]
  let mut omitted := 0
  for (vcId, vc) in candidates do
    let hasPeerSource := (alternativePeerIds mgr vcId).any fun peerId =>
      sourceIds.contains peerId
    if sourceIds.contains vcId || hasPeerSource then
      eligible := eligible.push (vcId, vc)
    else
      omitted := omitted + 1
  return (eligible, omitted)

private def reserveGenTheoremCandidates
    (candidates : Array (VCId × VerificationCondition VCMetadata SmtResult)) :
    CommandElabM
      (Array ReservedVCTheorem × Array GenTheoremsDeclProgress × Nat × Std.HashSet VCId) := do
  liftTermElabM do
    let mut reserved := #[]
    let mut decls := #[]
    let mut existing := 0
    let mut availableIds : Std.HashSet VCId := Std.HashSet.emptyWithCapacity
    for (vcId, vc) in candidates do
      let some indMeta := inductionMetadata? vc
        | throwError "cannot generate VC theorem `{vc.name}` because it is not an induction VC"
      match ← reserveVCTheorem vcId vc with
      | .existing fullName =>
        existing := existing + 1
        availableIds := availableIds.insert vcId
        decls := decls.push { name := fullName, style := indMeta.style, status := .existing }
      | .reserved entry =>
        reserved := reserved.push entry
        decls := decls.push { name := entry.fullName, style := indMeta.style, status := .pending }
    return (reserved, decls, existing, availableIds)

private def equivalentWitnessForReserved
    (mgr : VCManager VCMetadata SmtResult) (availableIds : Std.HashSet VCId)
    (reserved : ReservedVCTheorem) : TermElabM (Option Witness) := do
  for sourceId in alternativePeerIds mgr reserved.vcId do
    unless availableIds.contains sourceId do
      continue
    let some sourceVC := mgr.nodes[sourceId]?
      | continue
    unless isBridgeableInductionPair sourceVC reserved.vc do
      continue
    if ← vcTheoremAvailable sourceVC then
      let sourceName ← vcTheoremFullName sourceVC
      if let some witness ← mkEquivalentInductionWitnessFromProof sourceVC reserved.vc (mkConst sourceName) then
        return some witness
  return none

private def witnessForReserved
    (mgr : VCManager VCMetadata SmtResult) (availableIds : Std.HashSet VCId)
    (reserved : ReservedVCTheorem) : TermElabM (Option Witness) := do
  setEnv reserved.async.asyncEnv
  if let some (_, witness) := mgr.provenWitness? reserved.vcId then
    return some (← instantiateMVars witness)
  equivalentWitnessForReserved mgr availableIds reserved

private def setDeclStatus
    (decls : Array GenTheoremsDeclProgress) (fullName : Name)
    (status : GenTheoremsDeclStatus) : Array GenTheoremsDeclProgress :=
  decls.map fun decl =>
    if decl.name == fullName then
      { decl with status := status }
    else
      decl

private def markGenerated (progressRef : GenTheoremsProgressRef) (fullName : Name) : BaseIO Unit :=
  progressRef.modify fun p => {
    p with
      generated := p.generated + 1
      decls := setDeclStatus p.decls fullName .generated
  }

private def markFailed
    (progressRef : GenTheoremsProgressRef) (fullName : Name) (msg : String) : BaseIO Unit :=
  progressRef.modify fun p => {
    p with
      failed := p.failed + 1
      decls := setDeclStatus p.decls fullName .failed
      failures := p.failures.push msg
  }

private def completeReservedWithRecovery (reserved : ReservedVCTheorem) : CommandElabM Unit := do
  liftTermElabM <| commitReservedVCTheorem reserved (sorryProof reserved.statement)

private def vcDoneOrDormant (mgr : VCManager VCMetadata SmtResult) (vcId : VCId) : Bool :=
  mgr._doneWith.contains vcId || mgr.dormantVCs.contains vcId

private def reservedCannotProduceLater
    (mgr : VCManager VCMetadata SmtResult) (reserved : ReservedVCTheorem) : Bool :=
  if mgr._doneWith.contains reserved.vcId then
    true
  else
    let peers := alternativePeerIds mgr reserved.vcId
    if mgr.dormantVCs.contains reserved.vcId &&
        peers.any (fun peerId => mgr._doneWith[peerId]? == some .proven) then
      true
    else if !vcHasDirectGenSource mgr reserved.vcId && !peers.isEmpty &&
        peers.all (vcDoneOrDormant mgr ·) then
      true
    else
      false

private def tryGenerateReservedTheorem
    (stx : Syntax) (progressRef : GenTheoremsProgressRef)
    (mgr : VCManager VCMetadata SmtResult) (availableIds : Std.HashSet VCId)
    (reserved : ReservedVCTheorem) : CommandElabM GenTheoremAttempt := do
  try
    match ← liftTermElabM <| witnessForReserved mgr availableIds reserved with
    | some witness => do
      liftTermElabM <| commitReservedVCTheorem reserved witness
      markGenerated progressRef reserved.fullName
      return .generated
    | none => do
      if reservedCannotProduceLater mgr reserved then
        let msg := s!"cannot generate VC theorem `{reserved.fullName}` because no proof witness is available"
        logErrorAt stx msg
        completeReservedWithRecovery reserved
        markFailed progressRef reserved.fullName msg
        return .failed
      return .pending
  catch ex =>
    let msg := s!"cannot generate VC theorem `{reserved.fullName}`: {← ex.toMessageData.toString}"
    logErrorAt stx msg
    try
      completeReservedWithRecovery reserved
    catch _ =>
      pure ()
    markFailed progressRef reserved.fullName msg
    return .failed

private partial def generateReservedTheoremsIncrementally
    (stx : Syntax) (progressRef : GenTheoremsProgressRef)
    (pending : Array ReservedVCTheorem) (availableIds : Std.HashSet VCId) : CommandElabM Unit := do
  progressRef.modify fun p => { p with phase := .generatingTheorems }
  logPendingDischargerTasks
  let mgr ← vcManager.atomically fun ref => ref.get
  let directReady := pending.filter fun entry =>
    (mgr.provenWitness? entry.vcId).isSome
  let otherPending := pending.filter fun entry =>
    (mgr.provenWitness? entry.vcId).isNone
  let toTry := if directReady.isEmpty then otherPending else directReady
  let deferred := if directReady.isEmpty then #[] else otherPending
  let mut nextPending := #[]
  let mut availableIds := availableIds
  for entry in toTry do
    match ← tryGenerateReservedTheorem stx progressRef mgr availableIds entry with
    | .generated =>
      availableIds := availableIds.insert entry.vcId
    | .failed =>
      pure ()
    | .pending =>
      nextPending := nextPending.push entry
  nextPending := nextPending ++ deferred
  if nextPending.isEmpty then
    progressRef.modify fun p => { p with phase := .done }
  else
    IO.sleep 100
    generateReservedTheoremsIncrementally stx progressRef nextPending availableIds

private def recoverReservedTheoremsAfterFatalError
    (reserved : Array ReservedVCTheorem) : CommandElabM Unit := do
  for entry in reserved do
    try
      completeReservedWithRecovery entry
    catch _ =>
      pure ()

def startGenTheoremsAsync (stx : Syntax) : CommandElabM GenTheoremsProgressRef := do
  let filter := VCMetadata.isInduction
  let allCandidates ← collectGenTheoremCandidates filter
  let (candidates, omitted) ← filterGeneratableTheoremCandidates allCandidates
  let (reserved, decls, existing, availableIds) ← reserveGenTheoremCandidates candidates
  let startTimeMs ← IO.monoMsNow
  let progressRef ← IO.mkRef {
    phase := if reserved.isEmpty then .done else .waitingForVCs
    total := candidates.size
    omitted := omitted
    existing := existing
    reserved := reserved.size
    decls := decls
    startTimeMs := startTimeMs
  }
  unless reserved.isEmpty do
    startFiltered filter
    let cancelTk ← IO.CancelToken.new
    let wrappedTask ← Command.wrapAsyncAsSnapshot (fun () => do
      try
        generateReservedTheoremsIncrementally stx progressRef reserved availableIds
      catch ex =>
        recoverReservedTheoremsAfterFatalError reserved
        let msg := s!"#gen_theorems failed: {← ex.toMessageData.toString}"
        progressRef.modify fun p =>
          let pending := p.decls.foldl (init := 0) fun acc decl =>
            acc + if decl.status == .pending then 1 else 0
          {
            p with
            phase := .done
            failed := p.failed + pending
            decls := p.decls.map fun decl =>
              if decl.status == .pending then { decl with status := .failed } else decl
            failures := p.failures.push msg
          }
        throw ex) cancelTk
    let task ← (wrappedTask ()).asTask (prio := .dedicated)
    Command.logSnapshotTask { stx? := none, cancelTk? := cancelTk, task := task }
  return progressRef

end Veil.Verifier
