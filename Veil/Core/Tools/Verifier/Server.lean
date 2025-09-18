import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Core.Tools.Verifier.Manager

namespace Veil

open Lean Elab Command
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
      dbg_trace "[Manager][dischargerLoop] RECV {res.kindString} notification from discharger {dischargerId}"
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

def sendFrontendNotification (notification : ManagerNotification VeilResult) : CommandElabM Unit := do
  let .some fch := (← getVCManager).fromFrontend | throwError "sendFrontendNotification called without a fromFrontend channel"
  let _ ← fch.send notification

end Veil
