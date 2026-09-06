import VeilTest.Regression.VerifierCancellationSupport

open Lean Elab Command Veil Veil.Verifier

private def awaitTestTask (task : Task α) : CommandElabM α := do
  let deadline ← (do IO.sleep 5000; pure (none : Option α)).asTask (prio := .dedicated)
  let some result ← IO.waitAny [task.map some, deadline]
    | throwError "verification regression timed out waiting for a synchronized task"
  return result

private def awaitResults : CommandElabM (VerificationResults VCMetadata SmtResult) := do
  let run ← Command.wrapAsync (fun () => waitFilteredSync (fun _ => true)) none
  let result ← awaitTestTask (← (run ()).toBaseIO.asTask (prio := .dedicated))
  match result with
  | .ok results => return results
  | .error ex => throw ex

private def addTestVC (name : Name) (term : Term) : CommandElabM Unit :=
  withVCManager fun ref => do
    let data : VCData VCMetadata := {name, params := #[], statement := ← `(term| True), metadata := default}
    let (mgr, id) := (← ref.get).addVC data {}
    let mgr ← mgr.mkAddDischarger id fun statement id ch =>
      Discharger.fromTermWith term statement id ch fun _ outcome time =>
        match outcome with
        | .inl witness => pure (.proven witness none time)
        | .inr ex => pure (.error #[(ex, toJson "failed test discharger")] time)
    ref.set mgr

run_cmd do
  -- Two modules remain live simultaneously; the first cannot become empty
  -- merely because the second starts, even when both use the same filter.
  runManager
  let first ← getSession
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  gates.set (some (entered, release))
  addTestVC `first (← `(term| by await_cancellation; trivial))
  let firstResult ← IO.Promise.new
  runFilteredAsync (fun _ => true) fun results => firstResult.resolve results.totalVCs
  let firstTask := (← get).snapshotTasks.back!.task
  let _ ← awaitTestTask entered.result?
  runManager
  let second ← getSession
  addTestVC `second (← `(term| by trivial))
  let result ← awaitResults
  unless result.totalVCs == 1 do throwError "second module got another module's results"
  unless (← first.snapshot).nodes.size == 1 do throwError "first module was discarded"
  unless (← first.snapshot)._managerId != (← second.snapshot)._managerId do throwError "session identities reused"
  release.resolve ()
  let _ ← awaitTestTask firstTask
  unless (← IO.hasFinished firstResult.result?) && firstResult.result?.get == some 1 do
    throwError "first module's callback lost its result"

run_cmd do
  -- Cancelling an overlapping waiter must not cancel work the other needs.
  runManager
  let session ← getSession
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  gates.set (some (entered, release))
  addTestVC `shared (← `(term| by await_cancellation; trivial))
  runFilteredAsync (fun _ => true) fun _ => pure ()
  let first := (← get).snapshotTasks.back!
  let result ← IO.Promise.new
  runFilteredAsync (fun _ => true) fun results => result.resolve results.totalVCs
  let second := (← get).snapshotTasks.back!
  let _ ← awaitTestTask entered.result?
  if let some tk := first.cancelTk? then tk.set
  let _ ← awaitTestTask first.task
  let mgr ← session.snapshot
  let some d := mgr.nodes[0]!.dischargers[0]? | throwError "missing discharger"
  unless !(← d.cancelTk.isSet) do
    throwError "cancelled one waiter's shared solver"
  release.resolve ()
  let _ ← awaitTestTask second.task
  unless (← IO.hasFinished result.result?) && result.result?.get == some 1 do
    throwError "surviving waiter failed to complete"

run_cmd do
  -- Standalone start helpers actually execute work without a result waiter.
  runManager
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  gates.set (some (entered, release))
  addTestVC `standalone (← `(term| by await_cancellation; trivial))
  startAll
  let _ ← awaitTestTask entered.result?
  release.resolve ()
  let result ← awaitResults
  unless result.totalVCs == 1 do throwError "standalone start did not run"

run_cmd do
  -- At capacity, an interactive proof supersedes a blocked automatic task;
  -- cancellation completion must refill the pool for the next enabled VC.
  let cores ← numCoresCache.get
  numCoresCache.set (some 1)
  try
    runManager
    let session ← getSession
    let entered ← IO.Promise.new
    let release ← IO.Promise.new
    gates.set (some (entered, release))
    addTestVC `automatic (← `(term| by await_cancellation; trivial))
    startAll
    let _ ← awaitTestTask entered.result?
    addTestVC `next (← `(term| by trivial))
    startAll
    session.withManager fun ref => do
      let mgr ← ref.get
      let vc := mgr.nodes[0]!
      let result : DischargerResult SmtResult := .proven (some (mkConst ``True.intro)) none 0
      let promise ← IO.Promise.new
      promise.resolve result
      let id : DischargerIdentifier := {
        managerId := mgr._managerId, vcId := 0, dischargerId := vc.dischargers.size, name := `manual }
      let d : Discharger SmtResult := {
        id, isInteractive := true, cancelTk := ← IO.CancelToken.new
        task := some (Task.pure default), startTimePromise := ← IO.Promise.new
        resultPromise := promise, mkTask := pure (Task.pure default) }
      let mgr := mgr.addDischarger 0 d
      ref.set (← mgr.recordDischargerResult id result)
    release.resolve ()
    let result ← awaitResults
    unless result.totalVCs == 2 && result.totalSolved == 2 do
      throwError "interactive supersession did not refill a full pool"
  finally
    numCoresCache.set cores

run_cmd do
  -- A delayed command runs against its captured environment, even after a
  -- new module starts. Its start notification cannot enable the new module.
  runManager
  let original ← getSession
  addTestVC `original (← `(term| by trivial))
  let delayedStart ← Command.wrapAsync (fun () => startAll) none
  runManager
  let replacement ← getSession
  addTestVC `replacement (← `(term| by trivial))
  let _ ← delayedStart ()
  let originalMgr ← original.snapshot
  let some d := originalMgr.nodes[0]!.dischargers[0]? | throwError "missing original discharger"
  let _ ← awaitTestTask d.resultPromise.result?
  unless (← replacement.snapshot).enabledVCs.isEmpty do
    throwError "old start notification enabled the replacement module"
  let _ ← awaitResults

run_cmd do
  -- Reset is explicit cancellation, never an empty successful result.
  runManager
  let session ← getSession
  addTestVC `cancelledSession (← `(term| by trivial))
  reset (← session.snapshot)._managerId
  let mut cancelled := false
  try
    let _ ← awaitResults
  catch ex =>
    cancelled := (← ex.toMessageData.toString).contains "cancelled"
  unless cancelled do throwError "reset was not surfaced as session cancellation"
