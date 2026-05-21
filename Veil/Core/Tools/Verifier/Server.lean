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

private def ensureExistingTheoremMatches (fullName : Name) (statement : Expr) : TermElabM Unit := do
  let some info := (← getEnv).find? fullName
    | return
  unless ← Meta.isDefEq info.type statement do
    throwError "cannot generate VC theorem `{fullName}` because a declaration with that name already exists with a different type"

private def vcTheoremFullName (vc : VerificationCondition VCMetadata SmtResult) : TermElabM Name := do
  return (← getCurrNamespace).append vc.name

private def vcTheoremAvailable (vc : VerificationCondition VCMetadata SmtResult) : TermElabM Bool := do
  let fullName ← vcTheoremFullName vc
  let some info := (← getEnv).find? fullName
    | return false
  Meta.isDefEq info.type (← vc.toVCStatement.type)

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
    let _ ← addVeilTheorem vc.name statement witness
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

private def mkEquivalentInductionWitness (source target : VerificationCondition VCMetadata SmtResult) :
    TermElabM (Option Witness) := do
  let some sourceMeta := inductionMetadata? source | return none
  let some targetMeta := inductionMetadata? target | return none
  unless isBridgeableInductionPair source target do
    return none
  let some derivedEqName ← derivedTransitionEqFullName? sourceMeta.action
    | return none
  let sourceName ← vcTheoremFullName source
  let sourceIdent := mkIdent sourceName
  let derivedEqIdent := mkIdent derivedEqName
  let assumingEqIdent := mkIdent (`Veil ++ `Transition ++ `meetsSpecificationIfSuccessfulAssuming_eq)
  let soundIdent := mkIdent (`Veil ++ `VeilM ++ `toTransitionDerived_sound)
  let proofStx? ← match sourceMeta.style, targetMeta.style with
    | .wp, .tr =>
      some <$> `(term| by
        simpa [← $assumingEqIdent:ident, $soundIdent:ident, $derivedEqIdent:ident] using $sourceIdent:ident)
    | .tr, .wp =>
      some <$> `(term| by
        simpa [$assumingEqIdent:ident, ← $soundIdent:ident, ← $derivedEqIdent:ident] using $sourceIdent:ident)
    | _, _ => pure none
  let some proofStx := proofStx?
    | return none
  let statement ← target.toVCStatement.type
  let witness ← instantiateMVars <| ← withSynthesize (postpone := .no) <|
    withoutErrToSorry $ elabTermEnsuringType proofStx statement
  if witness.hasMVar || witness.hasFVar || witness.hasSyntheticSorry then
    throwError "failed to generate equivalent VC theorem `{target.name}` from `{source.name}`"
  return some witness

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

end Veil.Verifier
