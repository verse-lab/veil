import VeilTest.Regression.VerifierCancellationSupport

open Lean Elab Command Veil Veil.Verifier

private def awaitTask (task : Task α) : CommandElabM α := do
  let deadline ← (do IO.sleep 5000; pure (none : Option α)).asTask (prio := .dedicated)
  let some result ← IO.waitAny [task.map some, deadline] | throwError "request rejection regression timed out"
  return result

run_cmd do
  runManager
  let session ← getSession
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  gates.set (some (entered, release))
  try
    withVCManager fun ref => do
      let data : VCData VCMetadata := {
        name := `valid, params := #[], statement := ← `(term| True)
        metadata := .induction { (default : InductionVCMetadata) with property := `valid } }
      let (mgr, id) := (← ref.get).addVC data {}
      let term ← `(term| by await_cancellation; trivial)
      let mgr ← mgr.mkAddDischarger id fun statement id ch =>
        Discharger.fromTermWith term statement id ch fun _ result time =>
          match result with
          | .inl witness => pure (.proven witness none time)
          | .inr ex => pure (.error #[(ex, toJson "test failed")] time)
      let (mgr, _) := mgr.addVC {data with name := `incomplete, metadata := default} {}
      ref.set mgr
    let result ← IO.Promise.new
    runFilteredAsync (·.propertyName? == some `valid) fun results => result.resolve results.totalSolved
    let waiter := (← get).snapshotTasks.back!
    let _ ← awaitTask entered.result?
    -- Rejected broad requests race with the active driver's demand refresh.
    -- They must never become visible to it or poison the valid request.
    for i in [:2000] do
      let mut rejected := false
      try
        if i % 2 == 0 then runFilteredAsync (fun _ => true) fun _ => pure ()
        else let _ ← waitFilteredSync (fun _ => true); pure ()
      catch _ => rejected := true
      unless rejected do throwError "incomplete registration was accepted"
      if i % 20 == 0 then IO.sleep 1
    let mgr ← session.snapshot
    let some d := mgr.nodes[0]!.dischargers[0]? | throwError "missing valid discharger"
    unless !(← d.cancelTk.isSet) do
      throwError "a rejected request cancelled another request's work"
    release.resolve ()
    let _ ← awaitTask waiter.task
    unless (← IO.hasFinished result.result?) && result.result?.get == some 1 do
      throwError "valid request failed after another request was rejected"
  finally
    release.resolve ()
