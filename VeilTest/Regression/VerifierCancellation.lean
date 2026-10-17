module

meta import VeilTest.Regression.VerifierCancellationSupport

/-!
Cancelled snapshot workers used to exit without publishing a discharger result,
leaving the manager waiting forever. Exercise the real worker and inspect its
promise and notification only after it exits, so the regression fails without
waiting on the missing result. No SMT solver is needed.
-/

open Lean Elab Command Veil
open VeilTest.VerifierCancellation

meta section

private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

-- Timing is only a bounded failure guard. Ordering comes from explicit gates
-- and waiting for the actual snapshot worker, never from a sleep.
private def awaitTask (name : String) (t : Task α) : IO α := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← IO.hasFinished t) do
    if (← IO.monoMsNow) > deadline then throw (IO.userError s!"timed out: {name}")
    IO.sleep 1
  IO.wait t

private inductive Scenario where
  | prestart | tacticInterrupt | resultInterrupt | lateCancel | success | handledFailure | nestedFailure
  deriving BEq

private def scenarioName : Scenario → String
  | .prestart => "pre-start cancellation"
  | .tacticInterrupt => "gated proof interruption"
  | .resultInterrupt => "gated mkResult interruption"
  | .lateCancel => "cancellation as mkResult returns"
  | .success => "ordinary success"
  | .handledFailure => "ordinary handled failure"
  | .nestedFailure => "nested mkResult failure"

private def runScenario (scenario : Scenario) : CommandElabM Unit := do
  let name := scenarioName scenario
  let ch ← Std.Channel.new (α := ManagerNotification VCMetadata SmtResult)
  let manager ← VCManager.new ch
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let calls ← IO.mkRef 0
  let cancelToken ← IO.mkRef (none : Option IO.CancelToken)
  let stmt : VCStatement := { name := `cancellationTest, params := #[], statement := ← `(True) }
  let term ← match scenario with
    | .tacticInterrupt => `(by cancellation_gate; exact True.intro)
    | .handledFailure => `(by exact (0 : Nat))
    | _ => `(True.intro)
  gates.set (some (entered, release))
  let d ← Discharger.fromTermWith term stmt
    { managerId := manager._managerId, vcId := 0, dischargerId := 0, name := `cancellationTest } ch
    (fun _ outcome time => do
      calls.modify (· + 1)
      if scenario == .resultInterrupt then
        entered.resolve ()
        let _ ← IO.wait release.result?
        Core.checkInterrupted
      if scenario == .nestedFailure then throwError "mkResult failed"
      if scenario == .lateCancel then
        let some token ← cancelToken.get | throwError "missing cancellation token"
        token.set
      match outcome with
      | .inl witness => return .proven (some witness) none time
      | .inr ex => return .error #[← safeExceptionEntry ex] time)
  cancelToken.set (some d.cancelTk)
  try
    if scenario == .prestart then d.cancelTk.set
    let d ← d.run
    if scenario == .tacticInterrupt || scenario == .resultInterrupt then
      let _ ← awaitTask s!"{name}: worker checkpoint" entered.result?
      let (mgr, _) := manager.addVC { stmt with metadata := (default : VCMetadata) } {} #[d]
      check ((← mgr.inFlightCount) == 1) s!"{name}: gated worker must occupy one slot"
      d.cancelTk.set
      release.resolve ()
    let _ ← awaitTask s!"{name}: worker exit" d.task.get!
    let finished ← IO.hasFinished d.resultPromise.result?
    let notification ← ch.tryRecv
    let duplicate ← ch.tryRecv
    let (mgr, _) := manager.addVC { stmt with metadata := (default : VCMetadata) } {} #[d]
    let inFlight ← mgr.inFlightCount
    liftIO <| IO.println s!"{name}: worker exited; published={finished}; notification={notification.isSome}; duplicate={duplicate.isSome}; inFlight={inFlight}"
    check finished s!"{name}: exited worker left result unresolved"
    check notification.isSome s!"{name}: no manager notification"
    check duplicate.isNone s!"{name}: duplicate manager notification"
    check (inFlight == 0) s!"{name}: exited worker still consumes capacity"
    let some res := d.resultPromise.result?.get
      | throwError "{name}: promise was dropped instead of published"
    let some (.dischargerResult id notified) := notification
      | throwError "{name}: wrong manager notification"
    check (id == d.id && notified.kindString == res.kindString && notified.time == res.time)
      s!"{name}: notification mismatch"
    let committed ← mgr.recordDischargerResult id notified
    check committed.isDone s!"{name}: accepting the event did not complete the VC"
    match scenario, res with
    | .success, .proven (some _) _ _ => check ((← calls.get) == 1) "success callback repeated"
    -- The next interruption checkpoint determines whether publication occurs
    -- inside or outside the snapshot wrapper. Both paths must publish once.
    | .lateCancel, .proven (some _) _ _ | .lateCancel, .error _ _ =>
      check ((← calls.get) == 1) "late cancellation repeated the result callback"
    | .nestedFailure, .error errors _ =>
      check (errors.size == 2 && (← calls.get) == 2) "nested failure lost either exception"
    | .handledFailure, .error errors _ =>
      check (errors.size == 1 && (← calls.get) == 1) "handled failure callback repeated"
    | .prestart, .error errors _ | .tacticInterrupt, .error errors _ | .resultInterrupt, .error errors _ =>
      check (!errors.isEmpty) s!"{name}: missing interruption diagnostic"
      let rendered := errors.map (·.2.compress)
      check (rendered.any fun message =>
        message.contains "interrupted" || message.contains "cancelled" ||
        message.contains "canceled" || message.contains "aborted")
        s!"{name}: unclear interruption diagnostic"
      let expectedCalls := if scenario == .resultInterrupt then 1 else 0
      check ((← calls.get) == expectedCalls) s!"{name}: unexpected result callback execution"
    | _, _ => throwError "{name}: unexpected result {res.kindString}"
  finally
    -- Keep the actual promises live until all observations, including baseline
    -- unresolved checks, finish. Dropping one can fake hasFinished via `none`.
    d.startTimePromise.resolve 0
    d.resultPromise.resolve (.unknown none 0)
    entered.resolve ()
    release.resolve ()
    gates.set none

run_cmd runScenario .prestart
run_cmd runScenario .tacticInterrupt
run_cmd runScenario .resultInterrupt
run_cmd runScenario .lateCancel
run_cmd runScenario .success
run_cmd runScenario .handledFailure
run_cmd runScenario .nestedFailure
