import VeilTest.Regression.VerifierCancellationSupport

open Lean Elab Command Veil Veil.Verifier

private def awaitTask (task : Task α) : CommandElabM α := do
  let deadline ← (do IO.sleep 5000; pure (none : Option α)).asTask (prio := .dedicated)
  let some result ← IO.waitAny [task.map some, deadline] | throwError "late registration regression timed out"
  return result

private def addTestVC (name : Name) (term : Term) : CommandElabM Unit :=
  withVCManager fun ref => do
    let data : VCData VCMetadata := {name, params := #[], statement := ← `(term| True), metadata := default}
    let (mgr, id) := (← ref.get).addVC data {}
    ref.set (← mgr.mkAddDischarger id fun statement id ch =>
      Discharger.fromTermWith term statement id ch fun _ outcome time =>
        match outcome with
        | .inl witness => pure (.proven witness none time)
        | .inr ex => pure (.error #[(ex, toJson "failed test discharger")] time))

run_cmd do
  runManager
  let session ← getSession
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  gates.set (some (entered, release))
  addTestVC `first (← `(term| by await_cancellation; trivial))
  let completed ← IO.Promise.new
  runFilteredAsync (fun _ => true) fun result => completed.resolve (result.totalVCs, result.totalSolved)
  let _ ← awaitTask entered.result?
  addTestVC `late (← `(term| by trivial))
  unless (← session.snapshot).enabledVCs.contains 1 do
    release.resolve ()
    throwError "live request did not enable its newly registered condition"
  release.resolve ()
  let result ← awaitTask completed.result?
  unless result == some (2, 2) do throwError "late registration stranded an existing waiter"
