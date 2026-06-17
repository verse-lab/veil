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

private def metadataToJsonFields {ρ σ κ : Type} (r : SimulateResult ρ σ κ) : List (String × Json) :=
  let reasonField := r.terminationReason.map fun reason => ("termination_reason", Lean.toJson reason)
  [
    ("traces_run", Lean.toJson r.tracesRun),
    ("max_traces", Lean.toJson r.maxTraces),
    ("elapsed_ms", Lean.toJson r.elapsedMs),
    ("seed", Lean.toJson r.seed),
    ("depth", Lean.toJson r.depth)
  ] ++ reasonField.toList

/-- Flatten the result object while keeping simulation metadata at the top level. -/
def SimulateResult.toDisplayJson {ρ σ κ : Type} [ToJson ρ] [ToJson σ] [ToJson κ]
  (r : SimulateResult ρ σ κ) : Json :=
  match resultToJson r.result with
  | Json.obj kvs => Json.mkObj <| kvs.toList ++ metadataToJsonFields r
  | other => Json.mkObj <| ("result", other) :: metadataToJsonFields r

instance instToJsonSimulateResult {ρ σ κ : Type} [ToJson ρ] [ToJson σ] [ToJson κ] : ToJson (SimulateResult ρ σ κ) where
  toJson r := SimulateResult.toDisplayJson r

end Veil.ModelChecker.Simulation
