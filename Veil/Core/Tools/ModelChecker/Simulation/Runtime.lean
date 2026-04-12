import Veil.Core.Tools.ModelChecker.Simulation.Path
import Veil.Core.Tools.ModelChecker.Simulation.Soundness
import Veil.Core.Tools.ModelChecker.Concrete.Progress

namespace Veil.ModelChecker.Simulation

private structure SimulationHooks (m : Type → Type) where
  shouldStop : Nat → m Bool
  onTraceProgress : Nat → m PUnit
  onViolation : m PUnit

private def simulateLoopM {m : Type → Type} [Monad m] {ρ σ κ : Type} {th₀ : ρ}
  (hooks : SimulationHooks m)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  (remaining : Nat)
  (traceIndex : Nat)
  [Inhabited σ]
  [Inhabited (κ × σ)]
  : m (SimulateResult ρ σ κ) := do
  if ← hooks.shouldStop traceIndex then
    return {
      result := .cancelled
      tracesRun := traceIndex
      elapsedMs := 0
      seed := cfg.seed
      depth := 0
    }
  match remaining with
  | 0 =>
      return {
        result := .noViolationFound cfg.maxTraces
          (.earlyTermination (.reachedDepthBound cfg.maxTraces))
        tracesRun := cfg.maxTraces
        elapsedMs := 0
        seed := cfg.seed
        depth := 0
      }
  | remaining + 1 =>
      hooks.onTraceProgress traceIndex
      match runTraceAtSeed sys params th cfg traceIndex with
      | some (result, stepsUsed) =>
          hooks.onViolation
          return {
            result := result
            tracesRun := traceIndex + 1
            elapsedMs := 0
            seed := cfg.seed
            depth := stepsUsed
          }
      | none =>
          simulateLoopM hooks sys params th cfg remaining (traceIndex + 1)
termination_by remaining

@[inline, specialize]
def simulateCore {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  [inhabσ : Inhabited σ]
  [inhabκσ : Inhabited (κ × σ)]
  : SimulateResult ρ σ κ :=
  Id.run <| simulateLoopM
    { shouldStop := fun _ => false
      onTraceProgress := fun _ => PUnit.unit
      onViolation := PUnit.unit }
    sys params th cfg cfg.maxTraces 0

@[inline, specialize]
def simulateWithProgress {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken)
  [inhabσ : Inhabited σ]
  [inhabκσ : Inhabited (κ × σ)]
  : IO (SimulateResult ρ σ κ) := do
  let actualSeed ← if cfg.seed == 0 then IO.rand 0 0xFFFFFFFFFFFFFFFF else pure cfg.seed
  let cfg := { cfg with seed := actualSeed }
  let startMs ← IO.monoMsNow
  let lastStatusUpdateRef ← IO.mkRef startMs
  let simResult ← simulateLoopM
    { shouldStop := fun _ => Veil.ModelChecker.Concrete.shouldStop cancelToken progressInstanceId
      onTraceProgress := fun tracesRun => do
        let now ← IO.monoMsNow
        let lastStatusUpdate ← lastStatusUpdateRef.get
        if now - lastStatusUpdate ≥ 100 then
          Veil.ModelChecker.Concrete.updateSimulationProgress progressInstanceId
            s!"Running random traces ({tracesRun}/{cfg.maxTraces})"
            tracesRun cfg.maxTraces 0
          lastStatusUpdateRef.set now
      onViolation := do
        Veil.ModelChecker.Concrete.setViolationFound progressInstanceId }
    sys params th cfg cfg.maxTraces 0
  return { simResult with elapsedMs := (← IO.monoMsNow) - startMs }

@[inline, specialize]
def simulate {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  [inhabσ : Inhabited σ]
  [inhabκσ : Inhabited (κ × σ)]
  : IO (SimulateResult ρ σ κ) := do
  let cancelToken ← IO.CancelToken.new
  simulateWithProgress sys params th cfg 0 cancelToken

private theorem simulateLoopM_id_check {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  [Inhabited σ] [Inhabited (κ × σ)]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig) :
  ∀ remaining traceIndex,
    ResultSoundB sys params
      (SimulateResult.result
        (Id.run <| simulateLoopM
          { shouldStop := fun _ => false
            onTraceProgress := fun _ => PUnit.unit
            onViolation := PUnit.unit }
          sys params th cfg remaining traceIndex)) = true := by
  intro remaining
  induction remaining with
  | zero =>
      intro traceIndex
      have hStop : Id.run false = false := rfl
      simp [simulateLoopM, ResultSoundB, hStop]
  | succ remaining ih =>
      intro traceIndex
      simp [simulateLoopM, Id.run]
      by_cases hTrace : runTraceAtSeed sys params th cfg traceIndex = none
      · simp [hTrace]
        exact ih (traceIndex + 1)
      · cases hRun : runTraceAtSeed sys params th cfg traceIndex with
        | none => contradiction
        | some pair =>
            rcases pair with ⟨result, depth⟩
            simp [hRun]
            exact runTraceAtSeed_check sys params th cfg traceIndex result depth hRun

theorem simulateCore_sound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  [Inhabited σ] [Inhabited (κ × σ)]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig) :
  ResultSound sys params (SimulateResult.result (simulateCore sys params th cfg)) := by
  exact resultSound_of_check_true sys params _ (simulateLoopM_id_check sys params th cfg cfg.maxTraces 0)

end Veil.ModelChecker.Simulation
