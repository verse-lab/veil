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

def reset : CommandElabM Unit := sendNotification .reset
def startAll : CommandElabM Unit := sendNotification .startAll
def startFiltered (filter : VCMetadata → Bool) : CommandElabM Unit := sendNotification (.startFiltered filter)

def isDoesNotThrow (m : VCMetadata) : Bool := m.propertyName? == some `doesNotThrow

/-- Starts a separate task (on a dedicated thread) that runs the VCManager.
If this is called multiple times, each call will reset the VC manager. -/
def runManager (cancelTk? : Option IO.CancelToken := none) : CommandElabM Unit := do
  let cancelTk := cancelTk?.getD (← IO.CancelToken.new)
  let managerLoop ← Command.wrapAsync (fun () => do
    -- dbg_trace "({← IO.monoMsNow}) [Manager] Starting manager loop"
    while true do
      -- blocks until we get a notification
      -- NOTE: this `get` is really problematic, as it increases the threadpool size
      let notification := (← vcManagerCh.recv).get
      match notification with
      | .dischargerResult dischargerId res => vcManager.atomically (fun ref => do
        let mut mgr ← ref.get
        if dischargerId.managerId != mgr._managerId then
          dbg_trace "({← IO.monoMsNow}) [Manager] RECV dischargerResult from manager ID {dischargerId.managerId} (our ID: {mgr._managerId}); ignoring"
          return
        mgr := {mgr with _totalDischarged := mgr._totalDischarged + 1}
        if res.isSuccessful then
          mgr := {mgr with _totalSolved := mgr._totalSolved + 1}
        dbg_trace "({← IO.monoMsNow}) [Manager] RECV {res.kindString} notification from discharger {dischargerId} after {res.time}ms (solved: {mgr._totalSolved}/{mgr.nodes.size})"
        mgr ← mgr.markDischarger dischargerId res
        -- Call start AFTER markDischarger so freshly woken alternatives can be scheduled
        mgr ← mgr.start (howMany := 1)
        ref.set mgr
        -- If we're done with all VCs, send a notification to the frontend
        if mgr.isDone then
          dbg_trace "({← IO.monoMsNow}) [Manager] SEND done notification doneWith: {mgr._doneWith.toArray}"
          Frontend.notifyDone)
      | .startAll => vcManager.atomically (fun ref => do
        let mut mgr ← ref.get
        dbg_trace "({← IO.monoMsNow}) [Manager] RECV startAll notification"
        mgr ← mgr.start (howMany := (← getNumCores))
        ref.set mgr)
      | .startFiltered filter => vcManager.atomically (fun ref => do
        let mut mgr ← ref.get
        mgr ← mgr.start (howMany := (← getNumCores)) (filter := filter)
        ref.set mgr
        if mgr.isDoneFiltered filter then Frontend.notifyDone)
      | .reset => vcManager.atomically (fun ref => do
        let mut mgr ← ref.get
        dbg_trace "({← IO.monoMsNow}) [Manager] RECV reset notification"
        mgr ← VCManager.new vcManagerCh
        ref.set mgr)
  ) cancelTk
  vcServerStarted.atomically (fun ref => do
    if !(← ref.get) then
      -- This starts the task
      dbg_trace "({← IO.monoMsNow}) [Manager] Starting manager loop"
      let _ ← EIO.asTask (managerLoop ())
    else
      dbg_trace "({← IO.monoMsNow}) [Manager] Manager loop already started; resetting state"
      reset
    ref.set true
  )

/-- Start VCs matching the filter and run the callback asynchronously when done.
Uses `wrapAsyncAsSnapshot` so that errors from the callback are reported to the user.
Note: Widget display does not work in the callback since it runs in an async context. -/
def runFilteredAsync (filter : VCMetadata → Bool)
    (callback : VerificationResults VCMetadata SmtResult → CommandElabM Unit) : CommandElabM Unit := do
  startFiltered filter
  let cancelTk ← IO.CancelToken.new
  let wrappedTask ← Command.wrapAsyncAsSnapshot (fun () => do
    vcManager.atomicallyOnce frontendNotification
      (fun ref => do let mgr ← ref.get; return mgr.isDoneFiltered filter)
      (fun ref => do
        let mgr ← ref.get
        let results ← liftCoreM (mgr.toResults filter)
        callback results)) cancelTk
  let task ← (wrappedTask ()).asTask
  Command.logSnapshotTask { stx? := none, cancelTk? := cancelTk, task := task }

/-- Start VCs matching the filter and wait synchronously for completion.
Returns the results on the main thread, allowing widget display.
Warning: This blocks the elaborator until all matching VCs complete. -/
def waitFilteredSync (filter : VCMetadata → Bool) : CommandElabM (VerificationResults VCMetadata SmtResult) := do
  startFiltered filter
  vcManager.atomicallyOnce frontendNotification
    (fun ref => do let mgr ← ref.get; return mgr.isDoneFiltered filter)
    (fun ref => do
      let mgr ← ref.get
      liftCoreM (mgr.toResults filter))

end Veil.Verifier
