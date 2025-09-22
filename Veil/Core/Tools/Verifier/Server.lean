import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Core.Tools.Verifier.Manager
import Std.Sync.Mutex

namespace Veil.Verifier

open Lean Elab Command Std

def sendFrontendNotification (notification : ManagerNotification VeilResult) : CommandElabM Unit := do
  let _ ← vcManagerCh.send notification

def reset : CommandElabM Unit := sendFrontendNotification .reset
def startAll : CommandElabM Unit := sendFrontendNotification .startAll

/-- Starts a separate task (on a dedicated thread) that runs the VCManager.
If this is called multiple times, each call will reset the VC manager. -/
def runManager (cancelTk? : Option IO.CancelToken := none) : CommandElabM Unit := do
  let cancelTk := cancelTk?.getD (← IO.CancelToken.new)
  let managerLoop ← Command.wrapAsync (fun () => do
    let mut startTime ← IO.monoMsNow
    dbg_trace "[Manager] Starting manager loop"
    while true do
      -- blocks until we get a notification
      -- NOTE: this `get` is really problematic, as it increases the threadpool size
      let notification := (← vcManagerCh.recv).get
      match notification with
      | .dischargerResult dischargerId res => vcManager.atomically (fun ref => do
        let mut mgr ← ref.get
        let timeStr := res.time.map (fun time => s!"{time}ms") |>.getD ""
        mgr := {mgr with _totalDischarged := mgr._totalDischarged + 1}
        if res.isSuccessful then
          mgr := {mgr with _totalSolved := mgr._totalSolved + 1}
        dbg_trace "[Manager] RECV {res.kindString} notification from discharger {dischargerId} after {timeStr} (solved: {mgr._totalSolved}/{mgr.nodes.size} in {(← IO.monoMsNow) - startTime}ms)"
        mgr ← mgr.start (howMany := 1)
        ref.set mgr)
      | .startAll => vcManager.atomically (fun ref => do
        let mut mgr ← ref.get
        dbg_trace "[Manager] RECV startAll notification"
        mgr ← mgr.start (howMany := 8)
        ref.set mgr)
      | .reset => vcManager.atomically (fun ref => do
        let mut mgr ← ref.get
        dbg_trace "[Manager] RECV reset notification"
        mgr ← VCManager.new vcManagerCh
        ref.set mgr)
  ) cancelTk
  vcServerStarted.atomically (fun ref => do
    if !(← ref.get) then
      -- This starts the task
      let _ ← EIO.asTask (managerLoop ()) Task.Priority.dedicated
    else
      -- This clears the VC manager
      reset
    ref.set true
  )

def addVC (vc : VCData VCMetadata) (dependsOn : HashSet VCId) (initialDischargers : Array (Discharger VeilResult) := #[]) (sendNotification : Bool := false): CommandElabM VCId := do
  let uid ← vcManager.atomically (fun ref => do
    let (mgr', uid) := (← ref.get).addVC vc dependsOn initialDischargers
    ref.set mgr'
    return uid
  )
  if sendNotification then
    startAll
  return uid

def mkAddDischarger (vcId : VCId) (mk : VCStatement → DischargerIdentifier → Std.Channel (ManagerNotification VeilResult) → CommandElabM (Discharger VeilResult)) (sendNotification : Bool := false) : CommandElabM Unit := do
  vcManager.atomically (fun ref => do
    let mgr' ← (← ref.get).mkAddDischarger vcId mk
    ref.set mgr'
  )
  if sendNotification then
    startAll

end Veil.Verifier
