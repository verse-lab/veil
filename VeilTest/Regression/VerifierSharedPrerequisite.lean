import VeilTest.Regression.VerifierCancellationSupport

open Lean Elab Command Veil Veil.Verifier

private def awaitTask (task : Task α) : CommandElabM α := do
  let deadline ← (do IO.sleep 5000; pure (none : Option α)).asTask (prio := .dedicated)
  let some result ← IO.waitAny [task.map some, deadline] | throwError "prerequisite regression timed out"
  return result

run_cmd do
  runManager
  let session ← getSession
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  gates.set (some (entered, release))
  withVCManager fun ref => do
    let mut mgr ← ref.get
    for name in [`root, `leaf] do
      let metadata : VCMetadata := .induction { (default : InductionVCMetadata) with property := name }
      let data : VCData VCMetadata := {name, params := #[], statement := ← `(term| True), metadata}
      let (next, id) := mgr.addVC data (if name == `root then {} else {0})
      let term ← if name == `root then `(term| by await_cancellation; trivial) else `(term| by trivial)
      mgr ← next.mkAddDischarger id fun statement id ch =>
        Discharger.fromTermWith term statement id ch fun _ outcome time =>
          match outcome with
          | .inl witness => pure (.proven witness none time)
          | .inr ex => pure (.error #[(ex, toJson "failed test discharger")] time)
    ref.set mgr
  runFilteredAsync (fun m => m.propertyName? == some `root) fun _ => pure ()
  let rootWaiter := (← get).snapshotTasks.back!
  let completed ← IO.Promise.new
  runFilteredAsync (fun m => m.propertyName? == some `leaf) fun result => completed.resolve result.totalSolved
  let leafWaiter := (← get).snapshotTasks.back!
  let _ ← awaitTask entered.result?
  if let some token := rootWaiter.cancelTk? then token.set
  let _ ← awaitTask rootWaiter.task
  let some d := (← session.snapshot).nodes[0]!.dischargers[0]? | throwError "missing prerequisite"
  unless !(← d.cancelTk.isSet) do throwError "cancellation killed a prerequisite needed by another request"
  release.resolve ()
  let _ ← awaitTask leafWaiter.task
  unless (← IO.hasFinished completed.result?) && completed.result?.get == some 1 do
    throwError "dependent request did not finish after shared prerequisite"
