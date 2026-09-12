import Veil.Core.Tools.ModelChecker.Simulation.Basic

namespace Veil.ModelChecker.Simulation
open Lean

/--
Render the verdict using the `ModelCheckingResult` encoding, so that both commands
produce the same shape for the cases they share.

The `none` case is deliberately built by hand rather than going through
`ModelCheckingResult.noViolationFound`: that constructor demands an explored-state
count and a `TerminationReason`, and simulation has neither. Simulation reports the
absence of a violation through `SimulateResult.terminationReason` and `tracesRun`
instead -- see the table on `SimulateResult`.
-/
private def resultToJson {ρ σ κ : Type} [ToJson ρ] [ToJson σ] [ToJson κ]
  (result : Option (SimulationResult ρ σ κ)) : Json :=
  match result with
  -- `Json.null` stands in for the state fingerprint, which simulation does not have.
  | some (.foundViolation violation trace) =>
      toJson (ModelCheckingResult.foundViolation Json.null violation (some trace) : ModelCheckingResult ρ σ κ Json)
  | some (.assumptionFailure violates) =>
      toJson (ModelCheckingResult.foundViolation Json.null (.assumptionFailure violates) none : ModelCheckingResult ρ σ κ Json)
  | some .cancelled =>
      toJson (ModelCheckingResult.cancelled : ModelCheckingResult ρ σ κ Json)
  | none => Json.mkObj [("result", "no_violation_found")]

private def metadataToJsonFields {ρ σ κ : Type} (r : SimulateResult ρ σ κ) : List (String × Json) :=
  let reasonField := r.terminationReason.map fun reason => ("termination_reason", Lean.toJson reason)
  -- Absent for the pure entry points, which do not collect depths.
  let histogramField :=
    if r.depthHistogram.counts.isEmpty then none
    else some ("depth_histogram", Json.mkObj [
      ("bucket_width", Lean.toJson r.depthHistogram.bucketWidth),
      ("counts", Lean.toJson r.depthHistogram.counts)])
  [
    ("traces_run", Lean.toJson r.tracesRun),
    ("max_traces", Lean.toJson r.maxTraces),
    ("elapsed_ms", Lean.toJson r.elapsedMs),
    ("seed", Lean.toJson r.seed)
  ] ++ reasonField.toList ++ histogramField.toList

/-- Flatten the result object while keeping simulation metadata at the top level. -/
def SimulateResult.toDisplayJson {ρ σ κ : Type} [ToJson ρ] [ToJson σ] [ToJson κ]
  (r : SimulateResult ρ σ κ) : Json :=
  match resultToJson r.result with
  | Json.obj kvs => Json.mkObj <| kvs.toList ++ metadataToJsonFields r
  | other => Json.mkObj <| ("result", other) :: metadataToJsonFields r

instance instToJsonSimulateResult {ρ σ κ : Type} [ToJson ρ] [ToJson σ] [ToJson κ] : ToJson (SimulateResult ρ σ κ) where
  toJson r := SimulateResult.toDisplayJson r

end Veil.ModelChecker.Simulation
