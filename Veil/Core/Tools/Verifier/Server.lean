import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Core.Tools.Verifier.Manager

namespace Veil.Verifier

open Lean Elab Command Std
/-- Starts a separate task (on a dedicated thread) that runs the VCManager.
This should only be called once! -/
def runManager (cancelTk? : Option IO.CancelToken := none) : CommandElabM Unit := do
  let cancelTk := cancelTk?.getD (← IO.CancelToken.new)
  let managerLoop ← Command.wrapAsync (fun () => do
    let mut totalDischarged := 0
    let mut startTime ← IO.monoMsNow
    while true do
      -- blocks until we get a notification
      -- NOTE: this `get` is really problematic, as it increases the threadpool size
      let notification := (← vcManagerCh.recv).get
      match notification with
      | .dischargerResult dischargerId res =>
        let mgr := (← vcManager.get)
        let timeStr := res.time.map (fun time => s!"{time}ms") |>.getD ""
        totalDischarged := totalDischarged + 1
        -- dbg_trace "[Manager] RECV {res.kindString} notification from discharger {dischargerId} after {timeStr} (solved: {totalDischarged}/{mgr.nodes.size} in {(← IO.monoMsNow) - startTime}ms)"
        let mgr' ← liftCoreM $ mgr.start (howMany := 1)
        vcManager.set mgr'
      | .startAll =>
        let mgr := (← vcManager.get)
        -- dbg_trace "[Manager] RECV startAll notification"
        let mgr' ← liftCoreM $ mgr.start (howMany := 8)
        vcManager.set mgr'
  ) cancelTk
  -- This starts the task
  let _ ← EIO.asTask (managerLoop ()) Task.Priority.dedicated

def sendFrontendNotification (notification : ManagerNotification VeilResult := .startAll) : CommandElabM Unit := do
  let _ ← vcManagerCh.send notification

def addVC (vc : VCData VCMetadata) (dependsOn : HashSet VCId) (initialDischargers : Array (Discharger VeilResult) := #[]) (sendNotification : Bool := false): CommandElabM VCId := do
  let (mgr', uid) := (← vcManager.get).addVC vc dependsOn initialDischargers
  vcManager.set mgr'
  if sendNotification then
    sendFrontendNotification
  return uid

def mkAddDischarger (vcId : VCId) (mk : VCStatement → DischargerIdentifier → Std.Channel (ManagerNotification VeilResult) → CommandElabM (Discharger VeilResult)) (sendNotification : Bool := false) : CommandElabM Unit := do
  let mgr' ← (← vcManager.get).mkAddDischarger vcId mk
  vcManager.set mgr'
  if sendNotification then
    sendFrontendNotification

end Veil.Verifier
