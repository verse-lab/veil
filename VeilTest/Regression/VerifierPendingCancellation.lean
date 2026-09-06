import VeilTest.Regression.VerifierCancellationSupport

open Lean Elab Command Veil Veil.Verifier

private def awaitTask (task : Task α) : CommandElabM α := do
  let deadline ← (do IO.sleep 5000; pure (none : Option α)).asTask (prio := .dedicated)
  let some result ← IO.waitAny [task.map some, deadline] | throwError "pending cancellation regression timed out"
  return result

run_cmd do
  let cores ← numCoresCache.get
  numCoresCache.set (some 1)
  try
    runManager
    let session ← getSession
    let entered ← IO.Promise.new
    let release ← IO.Promise.new
    gates.set (some (entered, release))
    withVCManager fun ref => do
      let mut mgr ← ref.get
      for name in [`first, `queued] do
        let data : VCData VCMetadata := {name, params := #[], statement := ← `(term| True), metadata := default}
        let (next, id) := mgr.addVC data {}
        let term ← `(term| by await_cancellation; trivial)
        mgr ← next.mkAddDischarger id fun statement id ch =>
          Discharger.fromTermWith term statement id ch fun _ outcome time =>
            match outcome with
            | .inl witness => pure (.proven witness none time)
            | .inr ex => pure (.error #[(ex, toJson "failed test discharger")] time)
      ref.set mgr
    runFilteredAsync (fun _ => true) fun _ => pure ()
    let waiter := (← get).snapshotTasks.back!
    let _ ← awaitTask entered.result?
    let before ← session.snapshot
    unless (← before.inFlightCount) == 1 do throwError "test did not fill capacity"
    if let some token := waiter.cancelTk? then token.set
    let _ ← awaitTask waiter.task
    for (_, vc) in before.nodes do
      let some d := vc.dischargers[0]? | throwError "missing discharger"
      unless ← d.cancelTk.isSet do
        throwError "cancelled request left queued work eligible to execute"
    release.resolve ()
    for (_, vc) in before.nodes do
      let some d := vc.dischargers[0]? | throwError "missing discharger"
      let _ ← awaitTask d.resultPromise.result?
  finally
    numCoresCache.set cores
