import Veil.Core.Tools.ModelChecker.Simulation.Basic
import Veil.Core.Tools.ModelChecker.Concrete.Core

namespace Veil.ModelChecker.Simulation

theorem randNat_lt_length {α : Type} (xs : List α) (h : xs ≠ []) (gen : StdGen) :
  (let p := randNat gen 0 (xs.length - 1); p.1 < xs.length) := by
  have hlen : 0 < xs.length := by simpa [List.length_pos_iff_ne_nil] using h
  have hk : xs.length - 1 + 1 = xs.length := Nat.sub_add_cancel (Nat.succ_le_of_lt hlen)
  unfold randNat
  simp [Nat.not_lt.mpr (Nat.zero_le (xs.length - 1)), hk]
  exact Nat.mod_lt _ hlen

private def SimulationResult.depth {ρ σ κ : Type} : SimulationResult ρ σ κ → Nat
  | .foundViolation _ trace => trace.steps.size + if trace.failingStep.isSome then 1 else 0
  | .cancelled => 0

@[inline, specialize]
def simulateOnceLoop {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (stepsLeft : Nat)
  (currSt : σ)
  (trace : Trace ρ σ κ)
  : StateM StdGen (Option (SimulationResult ρ σ κ)) := do
  match stepsLeft with
  | 0 => return none
  | stepsLeft + 1 =>
    let outcomes := sys.tr th currSt
    let (nexts, assertionFailures) := Veil.ModelChecker.Concrete.partitionExecutionOutcome outcomes
    match assertionFailures with
    | (label, exId, st) :: _ =>
        let failedTrace := { trace with failingStep := some { transitionLabel := label, nextState := st } }
        return some (.foundViolation (.assertionFailure exId) failedTrace)
    | [] =>
      match nexts with
      | [] =>
          if !params.terminating.holdsOn th currSt then
            return some (.foundViolation .deadlock trace)
          else
            return none
      | hd :: tl =>
        let nexts := hd :: tl
        have hNonempty : nexts ≠ [] := by simp
        let gen ← get
        let p := randNat gen 0 (nexts.length - 1)
        let idx := p.1
        let gen' := p.2
        have hlt : idx < nexts.length := by
          dsimp [idx, p]
          exact randNat_lt_length nexts hNonempty gen
        set gen'
        let (label, nextSt) := nexts.get ⟨idx, hlt⟩
        let trace := trace.push { transitionLabel := label, nextState := nextSt }
        let violations := violatedInvariantNames params th nextSt
        if !violations.isEmpty then
          return some (.foundViolation (.safetyFailure violations) trace)
        else
          simulateOnceLoop sys params th stepsLeft nextSt trace
termination_by stepsLeft

@[inline, specialize]
def simulateOnce {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (maxSteps : Nat)
  : StateM StdGen (Option (SimulationResult ρ σ κ)) := do
  let initStates := sys.initStates
  match initStates with
  | [] => return none
  | hd :: tl =>
      let initStates := hd :: tl
      have hNonempty : initStates ≠ [] := by simp
      let gen ← get
      let p := randNat gen 0 (initStates.length - 1)
      let idx := p.1
      let gen' := p.2
      have hlt : idx < initStates.length := by
        dsimp [idx, p]
        exact randNat_lt_length initStates hNonempty gen
      set gen'
      let initSt := initStates.get ⟨idx, hlt⟩
      let initTrace : Trace ρ σ κ := { theory := th, initialState := initSt, steps := #[] }
      let initViolations := violatedInvariantNames params th initSt
      if !initViolations.isEmpty then
        return some (.foundViolation (.safetyFailure initViolations) initTrace)
      else
        simulateOnceLoop sys params th maxSteps initSt initTrace

/--
Simulates the trace identified by `traceIndex` using seed `cfg.seed + traceIndex`.
Returns the first violation found by that trace together with its derived trace depth.
-/
def simulateTraceAtIndex {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  (traceIndex : Nat)
  : Option (SimulationResult ρ σ κ × Nat) :=
  let traceSeed := cfg.seed + traceIndex
  let (maybeResult, _) := (simulateOnce sys params th cfg.maxSteps).run (mkStdGen traceSeed)
  maybeResult.map (fun result => (result, SimulationResult.depth result))

end Veil.ModelChecker.Simulation
