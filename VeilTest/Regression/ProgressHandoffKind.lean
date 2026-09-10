import Veil

/-!
# Progress-instance behaviour around handoff

`resetProgressForHandoff` rebuilds the progress record when the default mode hands
over to the compiled binary. While `Progress` was a flat structure with an optional
`simulation` field, the rebuild silently dropped that field, so the panel rendered
the model checker's rows (Diameter / States Found / ...) for a `#simulate` run until
the compiled binary's first progress line arrived. `Progress` is now an inductive,
so the rebuild has to restate the kind and cannot fall back by accident.

Handoff itself needs a real compilation and so is not covered by the test suite;
this pins the part of it that can be exercised directly.
-/

open Veil.ModelChecker.Concrete

/-- Fail with a readable message; `assert!` panics with a backtrace instead. -/
private def expect (message : String) (cond : Bool) : IO Unit :=
  unless cond do throw (IO.userError message)

-- A simulation instance stays a simulation, keeping its configured trace budget
-- while the per-run counters restart with the compiled binary.
#eval do
  let (id, _) ← allocProgressInstance (.simulation {})
  updateSimulationProgress id "Running random traces (7/50)" 7 50 3
  let before ← getProgress id
  expect "a simulation instance must report simulation metrics" <|
    match before.details with
    | .simulation m => m.tracesRun == 7 && m.maxTraces == 50 && m.depth == 3
    | .modelCheck .. => false
  let _ ← resetProgressForHandoff id
  let after ← getProgress id
  expect "handoff must not turn a simulation into a model check" <|
    match after.details with
    | .simulation m => m.maxTraces == 50 && m.tracesRun == 0 && m.depth == 0
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

-- The Stop button must kill the background compilation too, not just the
-- interpreted search. Before `compilationCancelTokenRef` existed, the compilation
-- token was a local in the elaborator and `requestCancellation` could not reach it,
-- so a cancelled run left its `lake build` running to completion.
#eval do
  let (id, interpretedToken) ← allocProgressInstance (.simulation {})
  let compilationToken ← IO.CancelToken.new
  setCompilationCancelToken id (some compilationToken)
  let interpretedSet ← interpretedToken.isSet
  let compilationSet ← compilationToken.isSet
  expect "no token should be set before cancellation" (!interpretedSet && !compilationSet)
  requestCancellation id
  expect "cancelling must stop the interpreted run" (← interpretedToken.isSet)
  expect "cancelling must stop the background compilation" (← compilationToken.isSet)

-- Once compilation is over its token is cleared, and a later cancellation must not
-- reach back to it.
#eval do
  let (id, _) ← allocProgressInstance (.modelCheck {})
  let compilationToken ← IO.CancelToken.new
  setCompilationCancelToken id (some compilationToken)
  setCompilationCancelToken id none
  requestCancellation id
  let compilationSet ← compilationToken.isSet
  expect "a cleared compilation token must not be cancelled" (!compilationSet)
