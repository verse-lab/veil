import Veil.Core.Tools.ModelChecker.Simulation
import Veil.Frontend.DSL.Module.Util.CommandRunner

open Lean Elab Command Veil Veil.ModelChecker Veil.ModelChecker.Simulation
open Veil.ModelChecker.Concrete

private def expect (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)

private def testSystem (th : Bool) (states : List Unit) :
    EnumerableTransitionSystem Bool (List Bool) Unit (List Unit) Int Unit
      (List (Unit × ExecutionOutcome Int Unit)) th := {
  initStates := states
  tr := fun _ _ => [((), .success ())]
}

private def testParams : SearchParameters Bool Unit := {
  assumptions := [
    { name := `first, property := fun th => th = true },
    { name := `always, property := fun _ => True },
    { name := `second, property := fun th => th = true }]
  -- If exploration starts, even its first state violates this invariant.
  invariants := [{ name := `unreachable_check, property := fun _ _ => False }]
  earlyTerminationConditions := []
}

private def expectFailure (cfg : SimulateConfig) (result : SimulateResult Bool Unit Unit) : IO Unit := do
  expect "must report exactly the failed assumptions in declaration order" <|
    match result.result with
    | some (.assumptionFailure names) => names == [`first, `second]
    | _ => false
  expect "invalid theory must not attempt any traces" (result.tracesRun == 0)
  expect "invalid theory must not record any trace depths" (result.depthHistogram.total == 0)
  expect "assumption failure must take precedence over no initial states" result.terminationReason.isNone
  expect "failure must preserve seed and budget" (result.seed == cfg.seed && result.maxTraces == cfg.maxTraces)
  let json := toJson result
  expect "assumption failure must use the shared violation encoding"
    (json.getObjValD "violation" == toJson (ViolationKind.assumptionFailure [`first, `second]))
  expect "assumption failure has no execution trace" (json.getObjValD "trace" == .null)

-- Pure and IO entry points reject invalid theories, independently of initial
-- states, state constraints, and trace/step budgets.
#eval do
  for states in [[], [()]] do
    for prune in [false, true] do
      let params := { testParams with stateConstraints :=
        if prune == true then [{ property := fun _ _ => False }] else [] }
      for maxTraces in [0, 3] do
        for maxSteps in [0, 2] do
          let cfg : SimulateConfig := { seed := 7, maxTraces, maxSteps }
          let sys := testSystem false states
          expectFailure cfg (simulateCore sys params false cfg)
          expectFailure cfg (← simulate sys params false cfg)
          let (id, token) ← allocProgressInstance (.simulation {})
          expectFailure cfg (← simulateWithProgress sys params false cfg id token)
          expect "runtime rejection must prevent handoff" (← isViolationFound id)
          match (← getProgress id).details with
          | .simulation progress =>
              expect "live progress must retain the budget with zero traces"
                (progress.tracesRun == 0 && progress.maxTraces == maxTraces)
          | _ => throw (IO.userError "runtime rejection changed the progress kind")

-- Valid theories still run the requested traces through both APIs.
#eval do
  let cfg : SimulateConfig := { seed := 7, maxTraces := 3, maxSteps := 2 }
  let params := { testParams with invariants := [] }
  let sys := testSystem true [()]
  for result in [simulateCore sys params true cfg, ← simulate sys params true cfg] do
    expect "valid theories must run normally" <|
      match result.result with
      | none => result.tracesRun == 3 && result.terminationReason.isNone
      | _ => false

private def awaitTask (task : Task α) : IO α := do
  let start ← IO.monoMsNow
  while !(← IO.hasFinished task) do
    if (← IO.monoMsNow) - start > 10000 then throw (IO.userError "assumption handoff test timed out")
    IO.sleep 1
  IO.wait task

-- Force compilation to request handoff before the real simulation runtime
-- validates the theory. The assumption failure must win over handoff cancellation.
elab "test_simulate_assumption_handoff" : command => do
  let (id, token) ← allocProgressInstance (.simulation {})
  let ctx : Veil.CommandRunner.Context := {
    stx := ← getRef, instanceId := id, cancelToken := token, resultKind := .simulate }
  let started ← IO.Promise.new (α := Unit)
  let binaryCalls ← IO.mkRef (0 : Nat)
  let interpret : IO Json := do
    started.resolve ()
    let start ← IO.monoMsNow
    while !(← checkHandoffRequested id) do
      if (← IO.monoMsNow) - start > 10000 then throw (IO.userError "handoff was never requested")
      IO.sleep 1
    return toJson (← simulateWithProgress (testSystem false [()]) testParams false
      { seed := 7, maxTraces := 3, maxSteps := 2 } id token)
  let (interpreted, compiled) ← Veil.CommandRunner.runWithHandoff ctx interpret
    (do let _ ← awaitTask started.result!; return .built "unused")
    (fun _ => do binaryCalls.modify (· + 1); return .null)
  let _ ← awaitTask interpreted
  let _ ← awaitTask compiled
  expect "compiled execution must not replace the invalid-theory result" ((← binaryCalls.get) == 0)
  let json := (← getResultJson id).getD .null
  expect "assumption failure must remain the final result"
    (json.getObjValD "violation" == toJson (ViolationKind.assumptionFailure [`first, `second]))
  expect "rejected command must finish progress" (!(← getProgress id).isRunning)

/--
error: ❌ Violation: assumption_failure (violates: first, second)
Seed: 7
-/
#guard_msgs in test_simulate_assumption_handoff
