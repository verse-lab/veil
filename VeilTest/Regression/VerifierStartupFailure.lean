import VeilTest.Regression.VerifierCancellationSupport

open Lean Elab Command Veil Veil.Verifier

private def awaitTask (task : Task α) : CommandElabM α := do
  let deadline ← (do IO.sleep 5000; pure (none : Option α)).asTask (prio := .dedicated)
  let some result ← IO.waitAny [task.map some, deadline] | throwError "startup regression timed out"
  return result

run_cmd do
  for async in [false, true] do
    runManager
    let session ← getSession
    let entered ← IO.Promise.new
    let release ← IO.Promise.new
    gates.set (some (entered, release))
    withVCManager fun ref => do
      let data : VCData VCMetadata := {name := `startup, params := #[], statement := ← `(term| True), metadata := default}
      let (mgr, id) := (← ref.get).addVC data {}
      let term ← `(term| by await_cancellation; trivial)
      let mgr ← mgr.mkAddDischarger id fun statement id ch =>
        Discharger.fromTermWith term statement id ch fun _ outcome time =>
          match outcome with
          | .inl witness => pure (.proven witness none time)
          | .inr ex => pure (.error #[(ex, toJson "failed test discharger")] time)
      ref.set mgr
    -- Commit malformed registration to exercise rejection after acquiring a
    -- request. The validation exception must release that request's interest.
    try
      session.withManager fun ref => ref.modify fun mgr => {mgr with upstream := mgr.upstream.insert 0 {0}}
    catch _ => pure ()
    let mut rejected := false
    try
      if async then runFilteredAsync (fun _ => true) fun _ => pure ()
      else let _ ← waitFilteredSync (fun _ => true); pure ()
    catch _ => rejected := true
    unless rejected do throwError "invalid registration unexpectedly started"
    session.withManager fun ref => ref.modify fun mgr => {mgr with upstream := mgr.upstream.insert 0 {}}
    let some d := (← session.snapshot).nodes[0]!.dischargers[0]? | throwError "missing discharger"
    unless !(← d.cancelTk.isSet) do throwError "rejected startup poisoned an unstarted discharger"
    runFilteredAsync (fun _ => true) fun _ => pure ()
    let waiter := (← get).snapshotTasks.back!
    let _ ← awaitTask entered.result?
    if let some token := waiter.cancelTk? then token.set
    let _ ← awaitTask waiter.task
    unless ← d.cancelTk.isSet do
      throwError "failed startup retained a phantom request and prevented solver cancellation"
    release.resolve ()
    let _ ← awaitTask d.resultPromise.result?
