module
meta import VeilTest.Regression.VerifierRollbackSupport
open Lean Elab Command Veil Veil.Verifier
meta section
run_cmd do
  runManager
  let oldId := (← readVCManager)._managerId
  withVCManager fun ref => do
    let (mgr, _) := (← ref.get).addVC {
      name := `validationProof, params := #[], statement := ← `(reset_during_validation_type), metadata := default } {}
    ref.set mgr
  let messages := (← get).messages
  resetDuringValidation.set true
  try
    elabCommand (← `(command| @[veil] public theorem $(mkIdent `validationProof) : True := True.intro))
    unless (← readVCManager)._managerId != oldId do throwError "fixture did not reset during validation"
    let errors := (← get).messages.toArray.filter (·.severity == .error)
    unless ← errors.anyM (fun msg => return (← msg.data.toString).contains "reset during theorem validation") do
      throwError "stale witness was not rejected"
    unless (interactiveRegistrationsExt.getState (← getEnv)).isEmpty do
      throwError "reset validation committed an obsolete registration"
    IO.println "actual attribute reset during witness validation rejects old registration: PASS"
  finally
    resetDuringValidation.set false
    modify fun st => { st with messages }
