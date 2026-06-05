import Veil.Core.Tools.ModelChecker.Simulation.Basic
import Veil.Core.Tools.ModelChecker.Concrete.Core

namespace Veil.ModelChecker.Simulation

inductive StepDecision (σ κ : Type) where
  | assertionFailure (exId : Int) (step : Step σ κ)
  | deadlock
  | terminated
  | continue (nexts : List (κ × σ)) (hNonempty : nexts ≠ [])

def decideAtState {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (currSt : σ) : StepDecision σ κ :=
  let outcomes := sys.tr th currSt
  let (nexts, assertionFailures) := Veil.ModelChecker.Concrete.partitionExecutionOutcome outcomes
  match assertionFailures with
  | (label, exId, st) :: _ =>
      .assertionFailure exId { transitionLabel := label, nextState := st }
  | [] =>
      match nexts with
      | [] => if !params.terminating.holdsOn th currSt then .deadlock else .terminated
      | hd :: tl => .continue (hd :: tl) (by simp)

theorem decideAtState_assertionFailure_mem {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (currSt : σ)
  (exId : Int) (step : Step σ κ) :
  decideAtState sys params th currSt = .assertionFailure exId step ->
    (step.transitionLabel, ExecutionOutcome.assertionFailure exId step.nextState) ∈
      sys.tr th currSt := by
  intro h
  let outcomes := sys.tr th currSt
  cases hPart : Veil.ModelChecker.Concrete.partitionExecutionOutcome outcomes with
  | mk nexts assertionFailures =>
    cases assertionFailures with
    | nil =>
      cases nexts with
      | nil =>
          by_cases hTerm : params.terminating.holdsOn th currSt = false
          · have : False := by
              simp [decideAtState, outcomes, hPart, hTerm] at h
            exact False.elim this
          · have : False := by
              simp [decideAtState, outcomes, hPart, hTerm] at h
            exact False.elim this
      | cons hd tl =>
          have : False := by
            simp [decideAtState, outcomes, hPart] at h
          exact False.elim this
    | cons failed _ =>
      rcases failed with ⟨label, foundExId, foundSt⟩
      simp [decideAtState, outcomes, hPart] at h
      rcases h with ⟨rfl, rfl⟩
      have hFailed : (label, foundExId, foundSt) ∈
          (Veil.ModelChecker.Concrete.partitionExecutionOutcome outcomes).snd := by
        rw [hPart]
        simp
      simpa [outcomes] using
        (Veil.ModelChecker.Concrete.partitionExecutionOutcome.snd_spec outcomes label foundExId foundSt).mp hFailed

theorem decideAtState_continue_nexts {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (currSt : σ)
  (nexts : List (κ × σ)) (hNonempty : nexts ≠ []) :
  decideAtState sys params th currSt = .continue nexts hNonempty ->
    nexts = (Veil.ModelChecker.Concrete.partitionExecutionOutcome
      (sys.tr th currSt)).fst := by
  intro h
  let outcomes := sys.tr th currSt
  cases hPart : Veil.ModelChecker.Concrete.partitionExecutionOutcome outcomes with
  | mk foundNexts assertionFailures =>
    cases assertionFailures with
    | cons failed rest =>
        have : False := by
          rcases failed with ⟨label, exId, st⟩
          simp [decideAtState, outcomes, hPart] at h
        exact False.elim this
    | nil =>
      cases foundNexts with
      | nil =>
          by_cases hTerm : params.terminating.holdsOn th currSt = false
          · have : False := by
              simp [decideAtState, outcomes, hPart, hTerm] at h
            exact False.elim this
          · have : False := by
              simp [decideAtState, outcomes, hPart, hTerm] at h
            exact False.elim this
      | cons hd tl =>
          have h' := h
          simp [decideAtState, outcomes, hPart] at h'
          cases h'
          rfl

theorem randNat_lt_length {α : Type} (xs : List α) (h : xs ≠ []) (gen : StdGen) :
  (let p := randNat gen 0 (xs.length - 1); p.1 < xs.length) := by
  have hlen : 0 < xs.length := by simpa [List.length_pos_iff_ne_nil] using h
  have hk : xs.length - 1 + 1 = xs.length := Nat.sub_add_cancel (Nat.succ_le_of_lt hlen)
  unfold randNat
  simp [Nat.not_lt.mpr (Nat.zero_le (xs.length - 1)), hk]
  exact Nat.mod_lt _ hlen

structure PickedTransition {σ κ : Type} (nexts : List (κ × σ)) where
  value : κ × σ
  mem : value ∈ nexts

def pickNextTransition {σ κ : Type}
  (nexts : List (κ × σ)) (h : nexts ≠ []) : StateM StdGen (PickedTransition nexts) := do
  let gen ← get
  let p := randNat gen 0 (nexts.length - 1)
  let idx := p.1
  let gen' := p.2
  have hlt : idx < nexts.length := by
    dsimp [idx, p]
    exact randNat_lt_length nexts h gen
  set gen'
  return {
    value := nexts.get ⟨idx, hlt⟩
    mem := by exact List.get_mem nexts ⟨idx, hlt⟩
  }

theorem pickNextTransition_mem {σ κ : Type}
  (nexts : List (κ × σ)) (gen : StdGen) (h : nexts ≠ []) :
  ((pickNextTransition nexts h).run gen).1.value ∈ nexts :=
  ((pickNextTransition nexts h).run gen).1.mem

structure PickedInitState {σ : Type} (initStates : List σ) where
  value : σ
  mem : value ∈ initStates

def pickInitialState {σ : Type}
  (initStates : List σ) (h : initStates ≠ []) : StateM StdGen (PickedInitState initStates) := do
  let gen ← get
  let p := randNat gen 0 (initStates.length - 1)
  let idx := p.1
  let gen' := p.2
  have hlt : idx < initStates.length := by
    dsimp [idx, p]
    exact randNat_lt_length initStates h gen
  set gen'
  return {
    value := initStates.get ⟨idx, hlt⟩
    mem := by exact List.get_mem initStates ⟨idx, hlt⟩
  }

theorem pickInitialState_mem {σ : Type}
  (initStates : List σ) (gen : StdGen) (h : initStates ≠ []) :
  ((pickInitialState initStates h).run gen).1.value ∈ initStates :=
  ((pickInitialState initStates h).run gen).1.mem

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
    match decideAtState sys params th currSt with
    | .assertionFailure exId step =>
        let failedTrace := { trace with failingStep := some step }
        return some (.foundViolation (.assertionFailure exId) failedTrace)
    | .deadlock =>
        return some (.foundViolation .deadlock trace)
    | .terminated =>
        return none
    | .continue nexts hNonempty =>
        let picked ← pickNextTransition nexts hNonempty
        let (label, nextSt) := picked.value
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
      let picked ← pickInitialState (hd :: tl) (by simp)
      let initSt := picked.value
      let initTrace : Trace ρ σ κ := { theory := th, initialState := initSt, steps := #[] }
      let initViolations := violatedInvariantNames params th initSt
      if !initViolations.isEmpty then
        return some (.foundViolation (.safetyFailure initViolations) initTrace)
      else
        simulateOnceLoop sys params th maxSteps initSt initTrace

def runTraceAtSeed {ρ σ κ : Type} {th₀ : ρ}
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
