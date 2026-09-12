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
  terminationReason := some .noInitialStates
}

private def hasNoInitialStates {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀) : Bool :=
  sys.initStates.isEmpty

private structure SimulationHooks (m : Type → Type) [Monad m] where
  shouldStop : Nat → m Bool
  /-- Initialize trace collection only after the theory and initial states are checked. -/
  onStart : m PUnit := pure ()
  onTraceProgress : Nat → m PUnit := fun _ => pure ()
  /-- Called with the depth each completed trace reached, violation or not. -/
  onTraceComplete : Nat → m PUnit := fun _ => pure ()
  onViolation : m PUnit := pure ()

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
    }
  match remaining with
  | 0 =>
      return {
        result := none
        tracesRun := cfg.maxTraces
        maxTraces := cfg.maxTraces
        elapsedMs := 0
        seed := cfg.seed
      }
  | remaining + 1 =>
      hooks.onTraceProgress traceIndex
      let (violation?, depth) := simulateTraceAtIndex sys params th cfg traceIndex
      hooks.onTraceComplete depth
      match violation? with
      | some result =>
          hooks.onViolation
          return {
            result := some result
            tracesRun := traceIndex + 1
            maxTraces := cfg.maxTraces
            elapsedMs := 0
            seed := cfg.seed
          }
      | none =>
          simulateLoopM hooks sys params th cfg remaining (traceIndex + 1)
termination_by remaining

/-- Shared setup for pure and IO simulation. Validate the theory with the model
checker's evaluator before checking initial states, budgets, or cancellation. -/
private def simulateRunM {m : Type → Type} [Monad m] {ρ σ κ : Type} {th₀ : ρ}
  (hooks : SimulationHooks m)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  : m (SimulateResult ρ σ κ) := do
  match params.violatedAssumptions th with
  | violates@(_ :: _) =>
      hooks.onViolation
      return {
        result := some (.assumptionFailure violates)
        tracesRun := 0
        maxTraces := cfg.maxTraces
        elapsedMs := 0
        seed := cfg.seed
      }
  | [] =>
      let sys := restrictSystemByStateConstraints sys params th
      if hasNoInitialStates sys then return noInitialStatesResult cfg
      hooks.onStart
      simulateLoopM hooks sys params th cfg cfg.maxTraces 0

@[inline, specialize]
def simulateCommandSemantics {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (shouldStop : Nat → Bool)
  (cfg : SimulateConfig)
  : SimulateResult ρ σ κ :=
  simulateRunM
    ({ shouldStop } : SimulationHooks Id)
    sys params th cfg

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
  let lastStatusUpdateRef ← IO.mkRef startMs
  let histogramRef ← IO.mkRef ({} : Histogram)
  let simResult ← simulateRunM
    { shouldStop := fun _ => Veil.ModelChecker.Concrete.shouldStop cancelToken progressInstanceId
      onStart := histogramRef.set (depthHistogramFor cfg.maxSteps)
      onTraceProgress := fun tracesRun => do
        let now ← IO.monoMsNow
        let lastStatusUpdate ← lastStatusUpdateRef.get
        if now - lastStatusUpdate ≥ 100 then
          Veil.ModelChecker.Concrete.updateSimulationProgress progressInstanceId
            s!"Running random traces ({tracesRun}/{cfg.maxTraces})"
            tracesRun cfg.maxTraces (← histogramRef.get)
          lastStatusUpdateRef.set now
      onTraceComplete := fun depth => histogramRef.modify (·.record depth)
      onViolation := do
        Veil.ModelChecker.Concrete.setViolationFound progressInstanceId }
    sys params th cfg
  let simResult := { simResult with
    elapsedMs := (← IO.monoMsNow) - startMs
    depthHistogram := ← histogramRef.get }
  match simResult.result with
  | some .cancelled => pure ()
  | _ =>
      Veil.ModelChecker.Concrete.updateSimulationProgress progressInstanceId
        (match simResult.result with | some (.assumptionFailure _) => "Assumptions violated" | _ => "Complete")
        simResult.tracesRun simResult.maxTraces simResult.depthHistogram
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
    ReportedViolationSound sys params
      (SimulateResult.result
        (simulateLoopM
          ({ shouldStop } : SimulationHooks Id)
          sys params th cfg remaining traceIndex)) := by
  intro remaining
  induction remaining with
  | zero =>
      intro traceIndex
      cases hStop : shouldStop traceIndex <;>
        simp [simulateLoopM, hStop, ReportedViolationSound, bind, pure]
  | succ remaining ih =>
      intro traceIndex
      cases hStop : shouldStop traceIndex with
      | true =>
          simp [simulateLoopM, hStop, ReportedViolationSound, bind, pure]
      | false =>
          by_cases hTrace : (simulateTraceAtIndex sys params th cfg traceIndex).1 = none
          · simpa [simulateLoopM, hStop, hTrace, bind, pure] using ih (traceIndex + 1)
          · cases hRun : (simulateTraceAtIndex sys params th cfg traceIndex).1 with
            | none => contradiction
            | some result =>
                simpa [simulateLoopM, hStop, hRun, bind, pure] using
                  simulateTraceAtIndex_sound th sys params cfg traceIndex result hRun

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
  cases hAssumptions : params.violatedAssumptions th with
  | cons name names =>
      simp [simulateCommandSemantics, simulateRunM, bind, pure, hAssumptions, ReportedViolationSound]
  | nil =>
      let restrictedSys := restrictSystemByStateConstraints sys params th
      cases hNoInit : hasNoInitialStates restrictedSys with
      | true =>
          simp [simulateCommandSemantics, simulateRunM, pure, hAssumptions, restrictedSys,
            hNoInit, noInitialStatesResult, ReportedViolationSound]
      | false =>
          simpa [simulateCommandSemantics, simulateRunM, bind, pure, hAssumptions, restrictedSys, hNoInit] using
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
