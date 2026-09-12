import Veil

/-!
# Progress-instance behaviour around handoff

`resetProgressForHandoff` rebuilds the progress record when the default mode hands
over to the compiled binary. While `Progress` was a flat structure with an optional
`simulation` field, the rebuild silently dropped that field, so the panel rendered
the model checker's rows (Diameter / States Found / ...) for a `#simulate` run until
the compiled binary's first progress line arrived. `Progress` is now an inductive,
so the rebuild has to restate the kind and cannot fall back by accident.

The shared driver is exercised separately in CommandRunner.lean.
-/

open Veil.ModelChecker.Concrete

/-- Fail with a readable message; `assert!` panics with a backtrace instead. -/
private def expect (message : String) (cond : Bool) : IO Unit :=
  unless cond do throw (IO.userError message)

-- A simulation instance stays a simulation, keeping its configured trace budget
-- while the per-run counters restart with the compiled binary.
#eval do
  let (id, _) ← allocProgressInstance (.simulation {})
  updateSimulationProgress id "Running random traces (7/50)" 7 50 {}
  let before ← getProgress id
  expect "a simulation instance must report simulation metrics" <|
    match before.details with
    | .simulation m => m.tracesRun == 7 && m.maxTraces == 50
    | .modelCheck .. => false
  let _ ← resetProgressForHandoff id
  let after ← getProgress id
  expect "handoff must not turn a simulation into a model check" <|
    match after.details with
    | .simulation m => m.maxTraces == 50 && m.tracesRun == 0
    | .modelCheck .. => false

-- A model check instance stays a model check, keeping the action labels it needs
-- to report never-enabled actions.
#eval do
  let (id, _) ← allocProgressInstance (.modelCheck { allActionLabels := ["Label.a", "Label.b"] })
  updateModelCheckProgress id 2 10 8 3
  let _ ← resetProgressForHandoff id
  let after ← getProgress id
  expect "handoff must not turn a model check into a simulation" <|
    match after.details with
    | .modelCheck m => m.allActionLabels == ["Label.a", "Label.b"] && m.diameter == 0
    | .simulation .. => false

-- Handoff stops both engines through shouldStop, without cancelling the command.
#eval do
  let (id, token) ← allocProgressInstance (.simulation {})
  requestHandoff id
  expect "handoff must stop interpreted exploration" (← shouldStop token id)
  expect "handoff must not cancel the compiler or binary" (!(← token.isSet))
  resetProgressForHandoff id
  expect "reset must clear the handoff request" (!(← checkHandoffRequested id))
  expect "the original token must remain usable after handoff" (!(← shouldStop token id))
  requestCancellation id
  expect "Stop after handoff must set the original token" (← token.isSet)

-- A Stop request during handoff survives the reset; tokens are never replaced.
#eval do
  let (id, token) ← allocProgressInstance (.modelCheck {})
  requestHandoff id
  requestCancellation id
  resetProgressForHandoff id
  expect "handoff must not erase cancellation" (← shouldStop token id)
  expect "all workers keep the same cancellation token" (← token.isSet)

-- Cancellation retains the full simulation payload in the final result.
#eval do
  let (id, _) ← allocProgressInstance (.simulation {})
  let json := Lean.Json.mkObj [("result", "cancelled"), ("seed", Lean.toJson (7 : Nat)),
    ("traces_run", Lean.toJson (3 : Nat))]
  cancelProgress id json
  let p ← getProgress id
  expect "cancelled progress must be terminal" (p.isCancelled && !p.isRunning)
  expect "final cancellation metadata must be retained" ((← getResultJson id) == some json)
