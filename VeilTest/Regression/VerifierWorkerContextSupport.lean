module
public meta import Veil.Frontend.DSL.Module.VCGen.Common

public theorem workerAvailable : True := True.intro

public meta section
open Lean Elab Tactic Veil
initialize workerContextGates : IO.Ref (Option (IO.Promise Unit × IO.Promise Unit)) ← IO.mkRef none

elab "worker_context_probe" : tactic => do
  unless (Veil.Verifier.vcManagerExt.getState (← getEnv)).isEmpty do
    throwError "worker captured mutable manager handles"
  unless (Veil.Verifier.interactiveRegistrationsExt.getState (← getEnv)).isEmpty do
    throwError "worker captured checkpoint proof registrations"
  unless (← getEnv).contains ``workerAvailable do
    throwError "worker lost ordinary theorem environment"
  if (← getInfoState).enabled then throwError "worker changed caller info recording configuration"
  logInfo "worker context diagnostic"
  let some (entered, release) ← workerContextGates.get | throwError "missing worker gates"
  entered.resolve ()
  let _ ← IO.wait release.result?
