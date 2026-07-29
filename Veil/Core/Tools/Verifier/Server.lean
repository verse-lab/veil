import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Core.Tools.Verifier.Manager
import Veil.Core.Tools.Verifier.Results
import Std.Sync.Mutex
import Veil.Util.Multiprocessing
import Veil.Util.Meta

namespace Veil.Verifier

open Lean Elab Command Std

-- FIXME: this should be in `EnvExtensions.lean`, but putting it there triggers
-- the bug fixed in [#10217](https://github.com/leanprover/lean4/pull/10217).
-- Placing it here as a workaround until the fix ships in a stable Lean.
/-- Holds the state of the VCManager for the current file. -/
initialize vcManager : Std.Mutex (VCManager VCMetadata SmtResult) ← Std.Mutex.new (← VCManager.new vcManagerCh)

/-- Errors thrown inside the manager loop. The loop runs detached from any
command snapshot (registering its infinite task would hang the build), so
exceptions it catches are invisible to the editor; they are recorded here and
surfaced as warnings by `awaitFilteredWithLogging` on its next poll. -/
initialize managerLoopErrors : IO.Ref (Array String) ← IO.mkRef #[]

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

/-- Start up to `count` ready dischargers matching `filter`: spawn each task
(`Discharger.run` only *spawns* — the elaboration/solving runs on the thread
pool), send it to the task registration channel for the frontend to register
via `logSnapshotTask`, and write the started discharger back into its node.

Must be called with the `vcManager` lock held, as part of a handler's single
critical section: holding the lock, the `(vc, discharger)` pairs returned by
`readyTasks` are *current*, so the write-back cannot clobber concurrent
frontend updates (interactive `@[veil]` registrations, added dischargers, a
reset) — the lost-update interleavings the old unlock-between-phases structure
allowed. The caller is responsible for `ref.set` of the returned manager. -/
private def startReadyTasksLocked (mgr : VCManager VCMetadata SmtResult)
    (count : Nat) (filter : VCMetadata → Bool := fun _ => true)
    : CommandElabM (VCManager VCMetadata SmtResult) := do
  let mut mgr := mgr
  let ready := (← mgr.readyTasks filter).take count
  for (vc, discharger) in ready do
    let discharger' ← discharger.run
    if let some task := discharger'.task then
      -- Send to channel for frontend to register (instead of registering directly here)
      let _ ← Veil.taskRegistrationCh.send { task, cancelTk := discharger'.cancelTk }
    let vc' := { vc with dischargers := vc.dischargers.set! discharger.id.dischargerId discharger' }
    mgr := { mgr with nodes := mgr.nodes.insert vc.uid vc' }
  return mgr

/-- Cancel every discharger of `mgr` and drain queued-but-not-yet-registered
task registrations, cancelling each. Called by both reset paths so replacing
the manager state never leaks running work: tasks already registered with the
language server are cancelled by it on re-elaboration, but entries still queued
in `taskRegistrationCh` would otherwise never be registered *nor* cancelled,
and running dischargers would keep computing for a manager generation whose
results are ignored (see `Discharger.cancelTk` for the cancellation latency
contract). Public so reset behavior can be regression-tested deterministically
(`VeilTest/Regression/VerifierServerRaces.lean`). -/
def cancelAbandonedWork (mgr : VCManager VCMetadata SmtResult) : IO Unit := do
  mgr.cancelAllDischargers
  while true do
    match ← Veil.taskRegistrationCh.tryRecv with
    | some info => info.cancelTk.set
    | none => break

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
        -- Each notification is processed in ONE `vcManager.atomically` section:
        -- decisions (`readyTasks`) and write-backs see the same state, frontend
        -- writers (`withVCManager`, `@[veil]` registration, the frontend-side
        -- reset in `runManager`) are serialized against the whole handler, and
        -- the single `ref.set` at the end makes a failed handler roll back
        -- wholesale instead of leaving torn state. Holding the lock here is
        -- cheap: `Discharger.run` only spawns a task, channel sends are
        -- non-blocking, and discharger task bodies never take this mutex.
        match notification with
        | .dischargerResult dischargerId res => do
          vcManager.atomically (fun ref => do
            let mut mgr ← ref.get
            if dischargerId.managerId != mgr._managerId then
              return
            mgr ← mgr.recordDischargerResult dischargerId res
            -- Start ready tasks AFTER recordDischargerResult so freshly woken
            -- alternatives can be scheduled. Only start 1 at a time.
            mgr ← startReadyTasksLocked mgr 1
            ref.set mgr)
          Frontend.notify
        | .startAll => do
          let numCores ← getNumCores
          vcManager.atomically (fun ref => do
            ref.set (← startReadyTasksLocked (← ref.get) numCores))
          Frontend.notify
        | .startFiltered filter => do
          let numCores ← getNumCores
          vcManager.atomically (fun ref => do
            ref.set (← startReadyTasksLocked (← ref.get) numCores filter))
          -- Wake pollers (they re-check `isDoneFiltered` under their own lock)
          Frontend.notify
        | .reset managerId => vcManager.atomically (fun ref => do
          let mut mgr ← ref.get
          if mgr._managerId != managerId then
            return
          -- Reap abandoned work before dropping the only references to it
          cancelAbandonedWork mgr
          mgr ← VCManager.new vcManagerCh (currentManagerId := mgr._managerId)
          ref.set mgr)
      catch ex =>
        -- Log errors but continue processing to prevent the manager loop from
        -- dying. The single-`ref.set` discipline above means a failed handler
        -- left the manager unchanged. Nothing logged here reaches the editor
        -- (the loop is not registered with `logSnapshotTask`), so also record
        -- the error for `awaitFilteredWithLogging` to surface as a warning.
        let msg ← ex.toMessageData.toString
        dbg_trace "[VCManager] Error in manager loop: {msg}"
        managerLoopErrors.modify (·.push msg)
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
        -- Reap abandoned work before dropping the only references to it
        cancelAbandonedWork mgr
        let mgr ← VCManager.new vcManagerCh (currentManagerId := mgr._managerId)
        managerRef.set mgr)
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
    -- Surface manager-loop errors where the user is looking; the loop itself
    -- cannot log to the editor (it is not registered with `logSnapshotTask`).
    for err in ← managerLoopErrors.modifyGet fun errs => (errs, #[]) do
      logWarning m!"VC manager loop error: {err}"
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

private def addProvenVCTheorem (vc : VerificationCondition VCMetadata SmtResult)
    (witness : Witness) : CommandElabM Unit := do
  liftTermElabM do
    let fullName := (← getCurrNamespace).append vc.name
    let statement ← vc.toVCStatement.type
    if (← getEnv).contains fullName then
      ensureExistingTheoremMatches fullName statement
      return
    let witness ← instantiateMVars witness
    let _ ← addVeilTheorem vc.name statement witness
    return ()

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
      addProvenVCTheorem vc witness

end Veil.Verifier
