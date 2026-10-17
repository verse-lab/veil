import VeilTest.Regression.VerifierCancellationSupport

open Lean Elab Command Veil Veil.Verifier

private def awaitTask (task : Task α) : CommandElabM α := do
  let deadline ← (do IO.sleep 5000; pure (none : Option α)).asTask (prio := .dedicated)
  let some result ← IO.waitAny [task.map some, deadline] | throwError "review probe timed out"
  return result

run_cmd do
  runManager
  let session ← getSession
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  gates.set (some (entered, release))
  withVCManager fun ref => do
    let data : VCData VCMetadata := {name := `retry, params := #[], statement := ← `(term| True), metadata := default}
    let (mgr, id) := (← ref.get).addVC data {}
    ref.set (← mgr.mkAddDischarger id fun statement id ch => do
      Discharger.fromTermWith (← `(term| by await_cancellation; trivial)) statement id ch fun _ outcome time =>
        match outcome with
        | .inl witness => pure (.proven witness none time)
        | .inr ex => pure (.error #[(ex, toJson "failed test discharger")] time))
  runFilteredAsync (fun _ => true) fun _ => pure ()
  let waiter := (← get).snapshotTasks.back!
  let _ ← awaitTask entered.result?
  if let some token := waiter.cancelTk? then token.set
  let _ ← awaitTask waiter.task
  release.resolve ()
  let some d := (← session.snapshot).nodes[0]!.dischargers[0]? | throwError "missing discharger"
  let _ ← awaitTask d.resultPromise.result?
  let result ← waitFilteredSync (fun _ => true)
  unless result.totalSolved == 1 do throwError "a new verification request reused the cancelled attempt"
