import Veil

open Veil.ModelChecker
open Veil.ModelChecker.Simulation

/--
info: {"elapsed_ms":0,"num_traces":3,"result":"no_violation_found","seed":"1","traces_run":3}
-/
#guard_msgs in
#eval IO.println <| (Lean.toJson ({
  result := none
  tracesRun := 3
  numTraces := 3
  elapsedMs := 0
  seed := 1
} : SimulateResult Unit Unit Unit)).compress

/--
info: {"elapsed_ms":0,"num_traces":3,"result":"no_violation_found","seed":"1","traces_run":3}
-/
#guard_msgs in
#eval IO.println <| (SimulateResult.toDisplayJson ({
  result := none
  tracesRun := 3
  numTraces := 3
  elapsedMs := 0
  seed := 1
} : SimulateResult Unit Unit Unit)).compress

/--
info: {"elapsed_ms":0,"num_traces":3,"result":"no_violation_found","seed":"1","termination_reason":{"kind":"no_initial_states"},"traces_run":0}
-/
#guard_msgs in
#eval IO.println <| (Lean.toJson ({
  result := none
  tracesRun := 0
  numTraces := 3
  elapsedMs := 0
  seed := 1
  terminationReason := some .noInitialStates
} : SimulateResult Unit Unit Unit)).compress

/--
info: {"elapsed_ms":12,"num_traces":10,"result":"cancelled","seed":"7","traces_run":5}
-/
#guard_msgs in
#eval IO.println <| (Lean.toJson ({
  result := some .cancelled
  tracesRun := 5
  numTraces := 10
  elapsedMs := 12
  seed := 7
} : SimulateResult Unit Unit Unit)).compress

/--
info: {"elapsed_ms":0,"num_traces":3,"result":"found_violation","seed":"1","state_fingerprint":null,"trace":{"states":[{"fields":null,"index":0,"transition":"after_init"},{"fields":null,"index":1,"transition":null},{"failing":true,"fields":null,"index":2,"transition":null}],"theory":null},"traces_run":1,"violation":{"exception_id":5,"kind":"assertion_failure"}}
-/
#guard_msgs in
#eval IO.println <| (Lean.toJson ({
  result := some (.foundViolation (.assertionFailure 5) ({
    theory := ()
    initialState := ()
    steps := #[{ transitionLabel := (), nextState := () }]
    failingStep := some { transitionLabel := (), nextState := () }
  } : Trace Unit Unit Unit))
  tracesRun := 1
  numTraces := 3
  elapsedMs := 0
  seed := 1
} : SimulateResult Unit Unit Unit)).compress

/--
info: {"elapsed_ms":0,"num_traces":3,"result":"found_violation","seed":"1","state_fingerprint":null,"trace":null,"traces_run":0,"violation":{"kind":"assumption_failure","violates":["first","second"]}}
-/
#guard_msgs in
#eval IO.println <| (Lean.toJson ({
  result := some (.assumptionFailure [`first, `second])
  tracesRun := 0
  numTraces := 3
  elapsedMs := 0
  seed := 1
} : SimulateResult Unit Unit Unit)).compress

-- Seeds must cross the JSON boundary as decimal strings, including values beyond
-- JavaScript's safe integer range and the randomly generated UInt64 range.
#eval do
  for seed in [0, 1, 9007199254740991, 9007199254740993, 18446744073709551615,
      18446744073709551617] do
    for result in ([none, some .cancelled, some (.assumptionFailure [`invalid])] :
        List (Option (SimulationResult Unit Unit Unit))) do
      let json := Lean.toJson ({
        result, tracesRun := 0, numTraces := 1, elapsedMs := 0, seed
      } : SimulateResult Unit Unit Unit)
      let parsed ← IO.ofExcept (Lean.Json.parse json.compress)
      let encodedSeed ← IO.ofExcept (parsed.getObjValAs? String "seed")
      unless encodedSeed.toNat? == some seed do
        throw (IO.userError s!"seed changed during JSON serialization: {seed}")
      let message ← (Veil.TraceDisplay.formatResult .simulate parsed).toString
      unless message.endsWith s!"Seed: {seed}" do
        throw (IO.userError s!"seed changed in the text diagnostic: {message}")
