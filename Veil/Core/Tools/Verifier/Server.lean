import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Core.Tools.Verifier.Manager
import Veil.Core.Tools.Verifier.Results
import Std.Sync.Mutex
import Veil.Util.Multiprocessing

namespace Veil.Verifier

open Lean Elab Command Std

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
            mgr := {mgr with _totalDischarged := mgr._totalDischarged + 1}
            if res.isSuccessful then
              mgr := {mgr with _totalSolved := mgr._totalSolved + 1}
            -- dbg_trace "({← IO.monoMsNow}) [Manager] RECV {res.kindString} notification from discharger {dischargerId} after {res.time}ms (solved: {mgr._totalSolved}/{mgr.nodes.size})"
            mgr ← mgr.markDischarger dischargerId res
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
      vcManager.atomically (fun ref => do
        let mgr ← ref.get
        reset mgr._managerId
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

end Veil.Verifier
