import Veil.Core.Tools.ModelChecker.Simulation.Path
import Veil.Core.Tools.ModelChecker.Simulation.Soundness
import Veil.Core.Tools.ModelChecker.Concrete.Progress

namespace Veil.ModelChecker.Simulation

private def noInitialStatesResult {ρ σ κ : Type} (cfg : SimulateConfig) : SimulateResult ρ σ κ := {
  result := none
  tracesRun := 0
  maxTraces := cfg.maxTraces
  elapsedMs := 0
  seed := cfg.seed
  depth := 0
}

private def hasNoInitialStates {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀) : Bool :=
  sys.initStates.isEmpty

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
  : m (SimulateResult ρ σ κ) := do
  if ← hooks.shouldStop traceIndex then
    return {
      result := some .cancelled
      tracesRun := traceIndex
      maxTraces := cfg.maxTraces
      elapsedMs := 0
      seed := cfg.seed
      depth := 0
    }
  match remaining with
  | 0 =>
      return {
        result := none
        tracesRun := cfg.maxTraces
        maxTraces := cfg.maxTraces
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
            result := some result
            tracesRun := traceIndex + 1
            maxTraces := cfg.maxTraces
            elapsedMs := 0
            seed := cfg.seed
            depth := stepsUsed
          }
      | none =>
          simulateLoopM hooks sys params th cfg remaining (traceIndex + 1)
termination_by remaining

private def simulateLoopId {ρ σ κ : Type} {th₀ : ρ}
  (shouldStop : Nat → Bool)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  (remaining : Nat)
  (traceIndex : Nat)
  : SimulateResult ρ σ κ :=
  if shouldStop traceIndex then
    {
      result := some .cancelled
      tracesRun := traceIndex
      maxTraces := cfg.maxTraces
      elapsedMs := 0
      seed := cfg.seed
      depth := 0
    }
  else
    match remaining with
    | 0 =>
        {
          result := none
          tracesRun := cfg.maxTraces
          maxTraces := cfg.maxTraces
          elapsedMs := 0
          seed := cfg.seed
          depth := 0
        }
    | remaining + 1 =>
        match runTraceAtSeed sys params th cfg traceIndex with
        | some (result, stepsUsed) =>
            {
              result := some result
              tracesRun := traceIndex + 1
              maxTraces := cfg.maxTraces
              elapsedMs := 0
              seed := cfg.seed
              depth := stepsUsed
            }
        | none =>
            simulateLoopId shouldStop sys params th cfg remaining (traceIndex + 1)
termination_by remaining

@[inline, specialize]
def simulateCommandSemantics {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (shouldStop : Nat → Bool)
  (cfg : SimulateConfig)
  : SimulateResult ρ σ κ :=
  let sys := restrictSystemByStateConstraints sys params th
  if hasNoInitialStates sys then
    noInitialStatesResult cfg
  else
    simulateLoopId shouldStop sys params th cfg cfg.maxTraces 0

@[inline, specialize]
def simulateCore {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  : SimulateResult ρ σ κ :=
  simulateCommandSemantics sys params th (fun _ => false) cfg

@[inline, specialize]
def simulateWithProgress {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  (progressInstanceId : Nat)
  (cancelToken : IO.CancelToken)
  : IO (SimulateResult ρ σ κ) := do
  let actualSeed ← if cfg.seed == 0 then IO.rand 0 0xFFFFFFFFFFFFFFFF else pure cfg.seed
  let cfg := { cfg with seed := actualSeed }
  let startMs ← IO.monoMsNow
  let sys := restrictSystemByStateConstraints sys params th
  if hasNoInitialStates sys then
    let simResult := { noInitialStatesResult cfg with elapsedMs := (← IO.monoMsNow) - startMs }
    Veil.ModelChecker.Concrete.updateSimulationProgress progressInstanceId
      "Complete"
      simResult.tracesRun simResult.maxTraces simResult.depth
    return simResult
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
  let simResult := { simResult with elapsedMs := (← IO.monoMsNow) - startMs }
  match simResult.result with
  | some .cancelled => pure ()
  | _ =>
      Veil.ModelChecker.Concrete.updateSimulationProgress progressInstanceId
        "Complete"
        simResult.tracesRun simResult.maxTraces simResult.depth
  return simResult

@[inline, specialize]
def simulate {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  : IO (SimulateResult ρ σ κ) := do
  let cancelToken ← IO.CancelToken.new
  simulateWithProgress sys params th cfg 0 cancelToken

private theorem simulateLoopM_id_sound {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ]
  [Inhabited σ] [Inhabited (κ × σ)]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (cfg : SimulateConfig)
  (shouldStop : Nat → Bool) :
  ∀ remaining traceIndex,
    ReportedViolationSound sys params (SimulateResult.result (simulateLoopId shouldStop sys params th cfg remaining traceIndex)) := by
  intro remaining
  induction remaining with
  | zero =>
      intro traceIndex
      cases hStop : shouldStop traceIndex <;> simp [simulateLoopId, hStop, ReportedViolationSound]
  | succ remaining ih =>
      intro traceIndex
      cases hStop : shouldStop traceIndex with
      | true =>
          simp [simulateLoopId, hStop, ReportedViolationSound]
      | false =>
          by_cases hTrace : runTraceAtSeed sys params th cfg traceIndex = none
          · simpa [simulateLoopId, hStop, hTrace] using ih (traceIndex + 1)
          · cases hRun : runTraceAtSeed sys params th cfg traceIndex with
            | none => contradiction
            | some pair =>
                rcases pair with ⟨result, depth⟩
                simpa [simulateLoopId, hStop, hRun] using
                  runTraceAtSeed_sound th sys params cfg traceIndex result depth hRun

theorem simulateCommandSemantics_sound {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ]
  [Inhabited σ] [Inhabited (κ × σ)]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (shouldStop : Nat → Bool)
  (cfg : SimulateConfig) :
  ReportedViolationSound (restrictSystemByStateConstraints sys params th) params
    (SimulateResult.result (simulateCommandSemantics sys params th shouldStop cfg)) := by
  let restrictedSys := restrictSystemByStateConstraints sys params th
  cases hNoInit : hasNoInitialStates restrictedSys with
  | true =>
      simp [simulateCommandSemantics, restrictedSys, hNoInit, noInitialStatesResult, ReportedViolationSound]
  | false =>
      simpa [simulateCommandSemantics, restrictedSys, hNoInit] using
        simulateLoopM_id_sound th restrictedSys params cfg shouldStop cfg.maxTraces 0

theorem simulateCore_sound {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ]
  [Inhabited σ] [Inhabited (κ × σ)]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (cfg : SimulateConfig) :
  ReportedViolationSound (restrictSystemByStateConstraints sys params th) params
    (SimulateResult.result (simulateCore sys params th cfg)) := by
  simpa [simulateCore] using simulateCommandSemantics_sound th sys params (fun _ => false) cfg

end Veil.ModelChecker.Simulation
