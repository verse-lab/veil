import VeilTest.Regression.VerifierCancellationSupport

open Lean Elab Command Veil

private def checkCompletion (d : Discharger SmtResult)
    (ch : Std.Channel (ManagerNotification VCMetadata SmtResult)) : CommandElabM Unit := do
  let _ ← IO.wait d.task.get!
  unless ← IO.hasFinished d.resultPromise.result? do
    throwError "finished task left result promise unresolved"
  unless ((← d.status) matches .finished (.error _ _)) do
    throwError "cancelled discharger did not finish with an error"
  unless (← ch.tryRecv).isSome do
    throwError "cancelled discharger did not notify scheduler"
  unless (← ch.tryRecv).isNone do
    throwError "discharger published more than once"
  let vc : VerificationCondition Unit SmtResult := {
    uid := 0, name := `cancelled, params := #[], statement := ← `(term| True)
    metadata := (), dischargers := #[d] }
  let mgr : VCManager Unit SmtResult := { (default : VCManager Unit SmtResult) with nodes := (Std.HashMap.emptyWithCapacity).insert 0 vc }
  unless (← mgr.inFlightCount) == 0 do
    throwError "cancelled task still consumes a solver slot"

run_cmd do
  let statement : VCStatement := {name := `cancelled, params := #[], statement := ← `(term| True)}
  let id : DischargerIdentifier := {managerId := 1, vcId := 0, dischargerId := 0, name := `cancelled}
  let ch ← Std.Channel.new
  let d ← VCDischarger.fromTerm (← `(term| by trivial)) `keep statement id (ch := ch)
  d.cancelTk.set
  checkCompletion (← d.run) ch
  let ch ← Std.Channel.new
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  gates.set (some (entered, release))
  let d ← VCDischarger.fromTerm (← `(term| by await_cancellation)) `keep statement id (ch := ch)
  let d ← d.run
  let enteredFirst ← IO.waitAny [entered.result?.map (fun _ => true), d.task.get!.map (fun _ => false)]
  unless enteredFirst do
    let st ← d.status
    throwError "tactic did not enter: {match st with | .finished r => r.kindString | _ => "pending"}"
  d.cancelTk.set
  release.resolve ()
  checkCompletion d ch
  -- A normal successful run also publishes exactly once.
  let ch ← Std.Channel.new
  let d ← Discharger.fromTermWith (← `(term| by trivial)) statement id ch fun _ r time =>
    match r with
    | .inl witness => pure (.proven witness none time)
    | .inr ex => pure (.error #[(ex, toJson "unexpected error")] time)
  let d ← d.run
  let _ ← IO.wait d.task.get!
  unless ((← d.status) matches .finished (.proven _ _ _)) do
    if let .finished r ← d.status then throwError "expected proof: {r}"
    throwError "expected proof"
  unless (← ch.tryRecv).isSome && (← ch.tryRecv).isNone do throwError "expected one notification"
