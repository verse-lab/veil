import Veil.Core.Tools.ModelChecker.Simulation.Basic

namespace Veil.ModelChecker.Simulation
open Lean

private def resultToJson {ρ σ κ : Type} [ToJson ρ] [ToJson σ] [ToJson κ]
  (result : Option (SimulationResult ρ σ κ)) : Json :=
  match result with
  | some (.foundViolation violation trace) =>
      toJson (ModelCheckingResult.foundViolation Json.null violation (some trace) : ModelCheckingResult ρ σ κ Json)
  | some .cancelled =>
      toJson (ModelCheckingResult.cancelled : ModelCheckingResult ρ σ κ Json)
  | none => Json.mkObj [("result", "no_violation_found")]

instance instToJsonSimulateResult {ρ σ κ : Type} [ToJson ρ] [ToJson σ] [ToJson κ] : ToJson (SimulateResult ρ σ κ) where
  toJson r := Json.mkObj [
    ("result", resultToJson r.result),
    ("traces_run", Lean.toJson r.tracesRun),
    ("max_traces", Lean.toJson r.maxTraces),
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
        ("max_traces", Lean.toJson r.maxTraces),
        ("elapsed_ms", Lean.toJson r.elapsedMs),
        ("seed", Lean.toJson r.seed),
        ("depth", Lean.toJson r.depth)
      ]
  | other =>
      Json.mkObj [
        ("result", other),
        ("traces_run", Lean.toJson r.tracesRun),
        ("max_traces", Lean.toJson r.maxTraces),
        ("elapsed_ms", Lean.toJson r.elapsedMs),
        ("seed", Lean.toJson r.seed),
        ("depth", Lean.toJson r.depth)
      ]

end Veil.ModelChecker.Simulation
