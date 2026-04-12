import Veil.Core.Tools.ModelChecker.Simulation.Basic

namespace Veil.ModelChecker.Simulation
open Lean

private def earlyTerminationReasonToJson (reason : EarlyTerminationReason Unit) : Json :=
  match reason with
  | .foundViolatingState _ violates => Json.mkObj [
      ("kind", "found_violating_state"),
      ("state_fingerprint", Json.null),
      ("violates", toJson violates)
    ]
  | .deadlockOccurred _ => Json.mkObj [
      ("kind", "deadlock_occurred"),
      ("state_fingerprint", Json.null)
    ]
  | .assertionFailed _ exId => Json.mkObj [
      ("kind", "assertion_failed"),
      ("state_fingerprint", Json.null),
      ("exception_id", toJson exId)
    ]
  | .reachedDepthBound depth => Json.mkObj [
      ("kind", "reached_depth_bound"),
      ("depth", toJson depth)
    ]
  | .cancelled => Json.mkObj [("kind", "cancelled")]

private def terminationReasonToJson (reason : TerminationReason Unit) : Json :=
  match reason with
  | .exploredAllReachableStates => Json.mkObj [("kind", "explored_all_reachable_states")]
  | .earlyTermination condition => Json.mkObj [
      ("kind", "early_termination"),
      ("condition", earlyTerminationReasonToJson condition)
    ]

private def resultToJson {ρ σ κ : Type} [ToJson ρ] [ToJson σ] [ToJson κ]
  (result : ModelCheckingResult ρ σ κ Unit) : Json :=
  match result with
  | .foundViolation _ violation trace => Json.mkObj
      [ ("result", "found_violation")
      , ("violation", toJson violation)
      , ("trace", toJson trace)
      , ("state_fingerprint", Json.null)
      ]
  | .noViolationFound exploredStates reason => Json.mkObj
      [ ("result", "no_violation_found")
      , ("explored_states", toJson exploredStates)
      , ("termination_reason", terminationReasonToJson reason)
      ]
  | .cancelled => Json.mkObj [("result", "cancelled")]

instance instToJsonSimulateResult {ρ σ κ : Type} [ToJson ρ] [ToJson σ] [ToJson κ] : ToJson (SimulateResult ρ σ κ) where
  toJson r := Json.mkObj [
    ("result", resultToJson r.result),
    ("traces_run", Lean.toJson r.tracesRun),
    ("elapsed_ms", Lean.toJson r.elapsedMs),
    ("seed", Lean.toJson r.seed),
    ("depth", Lean.toJson r.depth)
  ]

def SimulateResult.toDisplayJson {ρ σ κ : Type} [ToJson ρ] [ToJson σ] [ToJson κ]
  (r : SimulateResult ρ σ κ) : Json :=
  match resultToJson r.result with
  | Json.obj kvs =>
      Json.mkObj <| kvs.toList ++ [
        ("traces_run", Lean.toJson r.tracesRun),
        ("elapsed_ms", Lean.toJson r.elapsedMs),
        ("seed", Lean.toJson r.seed),
        ("depth", Lean.toJson r.depth)
      ]
  | other =>
      Json.mkObj [
        ("result", other),
        ("traces_run", Lean.toJson r.tracesRun),
        ("elapsed_ms", Lean.toJson r.elapsedMs),
        ("seed", Lean.toJson r.seed),
        ("depth", Lean.toJson r.depth)
      ]

end Veil.ModelChecker.Simulation
