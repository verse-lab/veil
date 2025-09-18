import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Core.Tools.Verifier.Manager

namespace Veil.Verifier

open Lean Elab Command Std
/-- Starts a separate task (on a dedicated thread) that runs the VCManager.
This should only be called once! -/
def runManager (cancelTk? : Option IO.CancelToken := none) : CommandElabM Unit := do
  let cancelTk := cancelTk?.getD (← IO.CancelToken.new)
  let .some dch := (← getVCManager).fromDischargers | throwError "runManager called without a fromDischargers channel"
  let .some fch := (← getVCManager).fromFrontend | throwError "runManager called without a fromFrontend channel"

  let dischargerLoop ← Command.wrapAsync (fun () => do
    while true do
      -- blocks until we get a notification
      let .fromDischarger dischargerId res := (← dch.recv).get | continue
      let mgr := (← getVCManager)
      let timeStr := res.time.map (fun time => s!" ({time}ms)") |>.getD ""
      dbg_trace "[Manager][dischargerLoop] RECV {res.kindString} notification from discharger {dischargerId} {timeStr}"
  ) cancelTk
  -- This starts the task
  let _ ← EIO.asTask (dischargerLoop ()) Task.Priority.dedicated

  let frontEndLoop ← Command.wrapAsync (fun () => do
    while true do
      let .fromFrontend := (← fch.recv).get | continue
      dbg_trace "[Manager][frontEndLoop] RECV notification from frontend"
      let mgr ← liftCoreM $ (← getVCManager).executeAll
      setVCManager mgr
  ) cancelTk
  -- This starts the task
  let _ ← EIO.asTask (frontEndLoop ()) Task.Priority.dedicated

def sendFrontendNotification (notification : ManagerNotification VeilResult := .fromFrontend) : CommandElabM Unit := do
  let .some fch := (← getVCManager).fromFrontend | throwError "sendFrontendNotification called without a fromFrontend channel"
  let _ ← fch.send notification

def addVC (vc : VCData VCMetadata) (dependsOn : HashSet VCId) (initialDischargers : Array (Discharger VeilResult) := #[]) : CommandElabM VCId := do
  let (mgr', uid) := (← getVCManager).addVC vc dependsOn initialDischargers
  setVCManager mgr'
  sendFrontendNotification
  return uid

def mkAddDischarger (vcId : VCId) (mk : VCStatement → DischargerIdentifier → Std.Channel (ManagerNotification VeilResult) → CommandElabM (Discharger VeilResult)) : CommandElabM Unit := do
  let mgr' ← (← getVCManager).mkAddDischarger vcId mk
  setVCManager mgr'
  sendFrontendNotification

end Veil.Verifier
