import Veil.Core.Tools.ModelChecker.Simulation.Basic
import Veil.Core.Tools.ModelChecker.Concrete.Core

namespace Veil.ModelChecker.Simulation

inductive StepDecision (σ κ : Type) where
  | assertionFailure (exId : Int) (step : Step σ κ)
  | deadlock
  | terminated
  | continue (nexts : List (κ × σ)) (hNonempty : nexts ≠ [])

private def assertionFailureWitness {σ κ : Type} : κ × ExecutionOutcome Int σ → Option (Int × Step σ κ)
  | (label, .assertionFailure exId st) => some (exId, { transitionLabel := label, nextState := st })
  | _ => none

def decideAtState {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (currSt : σ) : StepDecision σ κ :=
  let outcomes := filterOutcomesByConstraints sys params th currSt
  let failingStep := outcomes.findSome? assertionFailureWitness
  match failingStep with
  | some (exId, step) => .assertionFailure exId step
  | none =>
      let (nexts, _) := Veil.ModelChecker.Concrete.partitionExecutionOutcome outcomes
      match nexts with
      | [] => if !params.terminating.holdsOn th currSt then .deadlock else .terminated
      | hd :: tl => .continue (hd :: tl) (by simp)

theorem decideAtState_assertionFailure_mem {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (currSt : σ)
  (exId : Int) (step : Step σ κ) :
  decideAtState sys params th currSt = .assertionFailure exId step ->
    (step.transitionLabel, ExecutionOutcome.assertionFailure exId step.nextState) ∈
      filterOutcomesByConstraints sys params th currSt := by
  intro h
  let outcomes := filterOutcomesByConstraints sys params th currSt
  cases hFind : outcomes.findSome? assertionFailureWitness with
  | none =>
      cases hNexts : (Veil.ModelChecker.Concrete.partitionExecutionOutcome outcomes).fst with
      | nil =>
          by_cases hTerm : params.terminating.holdsOn th currSt = false
          · have : False := by
              simp [decideAtState, outcomes, hFind, hNexts, hTerm] at h
            exact False.elim this
          · have : False := by
              simp [decideAtState, outcomes, hFind, hNexts, hTerm] at h
            exact False.elim this
      | cons hd tl =>
          have : False := by
            simp [decideAtState, outcomes, hFind, hNexts] at h
          exact False.elim this
  | some found =>
      rcases found with ⟨foundExId, foundStep⟩
      simp [decideAtState, outcomes, hFind] at h
      rcases h with ⟨rfl, rfl⟩
      obtain ⟨entry, hEntryMem, hEntryEq⟩ := List.exists_of_findSome?_eq_some hFind
      rcases entry with ⟨label, outcome⟩
      cases outcome <;> simp [assertionFailureWitness] at hEntryEq
      case assertionFailure exId' st =>
        rcases hEntryEq with ⟨rfl, rfl⟩
        simpa [outcomes] using hEntryMem

theorem decideAtState_continue_nexts {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (currSt : σ)
  (nexts : List (κ × σ)) (hNonempty : nexts ≠ []) :
  decideAtState sys params th currSt = .continue nexts hNonempty ->
    nexts = (Veil.ModelChecker.Concrete.partitionExecutionOutcome
      (filterOutcomesByConstraints sys params th currSt)).fst := by
  intro h
  let outcomes := filterOutcomesByConstraints sys params th currSt
  cases hFind : outcomes.findSome? assertionFailureWitness with
  | some found =>
      have : False := by
        simp [decideAtState, outcomes, hFind] at h
      exact False.elim this
  | none =>
      cases hNexts : (Veil.ModelChecker.Concrete.partitionExecutionOutcome outcomes).fst with
      | nil =>
          by_cases hTerm : params.terminating.holdsOn th currSt = false
          · have : False := by
              simp [decideAtState, outcomes, hFind, hNexts, hTerm] at h
            exact False.elim this
          · have : False := by
              simp [decideAtState, outcomes, hFind, hNexts, hTerm] at h
            exact False.elim this
      | cons hd tl =>
          have h' := h
          simp [decideAtState, outcomes, hFind, hNexts] at h'
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
  gen : StdGen

def pickNextTransition {σ κ : Type}
  (nexts : List (κ × σ)) (gen : StdGen) (h : nexts ≠ []) : PickedTransition nexts :=
  let p := randNat gen 0 (nexts.length - 1)
  let idx := p.1
  let gen' := p.2
  have hlt : idx < nexts.length := by
    dsimp [idx, p]
    exact randNat_lt_length nexts h gen
  { value := nexts.get ⟨idx, hlt⟩
    mem := by exact List.get_mem nexts ⟨idx, hlt⟩
    gen := gen' }

theorem pickNextTransition_mem {σ κ : Type}
  (nexts : List (κ × σ)) (gen : StdGen) (h : nexts ≠ []) :
  (pickNextTransition nexts gen h).value ∈ nexts :=
  (pickNextTransition nexts gen h).mem

structure PickedInitState {σ : Type} (initStates : List σ) where
  value : σ
  mem : value ∈ initStates
  gen : StdGen

def pickInitialState {σ : Type}
  (initStates : List σ) (gen : StdGen) (h : initStates ≠ []) : PickedInitState initStates :=
  let p := randNat gen 0 (initStates.length - 1)
  let idx := p.1
  let gen' := p.2
  have hlt : idx < initStates.length := by
    dsimp [idx, p]
    exact randNat_lt_length initStates h gen
  { value := initStates.get ⟨idx, hlt⟩
    mem := by exact List.get_mem initStates ⟨idx, hlt⟩
    gen := gen' }

theorem pickInitialState_mem {σ : Type}
  (initStates : List σ) (gen : StdGen) (h : initStates ≠ []) :
  (pickInitialState initStates gen h).value ∈ initStates :=
  (pickInitialState initStates gen h).mem

@[inline, specialize]
def simulateOnceLoop {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (stepsLeft : Nat)
  (currSt : σ)
  (trace : Trace ρ σ κ)
  (gen : StdGen)
  : Option (SimulationResult ρ σ κ) × StdGen × Nat :=
  match stepsLeft with
  | 0 => (none, gen, 0)
  | stepsLeft + 1 =>
    match decideAtState sys params th currSt with
    | .assertionFailure exId step =>
        let failedTrace := { trace with failingStep := some step }
        (some (.foundViolation (.assertionFailure exId) failedTrace), gen, trace.steps.size + 1)
    | .deadlock =>
        (some (.foundViolation .deadlock trace), gen, trace.steps.size)
    | .terminated =>
        (none, gen, trace.steps.size)
    | .continue nexts hNonempty =>
        let picked := pickNextTransition nexts gen hNonempty
        let (label, nextSt) := picked.value
        let gen := picked.gen
        let trace := trace.push { transitionLabel := label, nextState := nextSt }
        let violations := violatedInvariantNames params th nextSt
        if !violations.isEmpty then
          (some (.foundViolation (.safetyFailure violations) trace), gen, trace.steps.size)
        else
          simulateOnceLoop sys params th stepsLeft nextSt trace gen
termination_by stepsLeft

@[inline, specialize]
def simulateOnce {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (gen : StdGen)
  (maxSteps : Nat)
  : Option (SimulationResult ρ σ κ) × StdGen × Nat :=
  let initStates := filterInitStatesByConstraints sys params th
  match initStates with
  | [] => (none, gen, 0)
  | hd :: tl =>
      let picked := pickInitialState (hd :: tl) gen (by simp)
      let initSt := picked.value
      let gen := picked.gen
      let initTrace : Trace ρ σ κ := { theory := th, initialState := initSt, steps := #[] }
      let initViolations := violatedInvariantNames params th initSt
      if !initViolations.isEmpty then
        (some (.foundViolation (.safetyFailure initViolations) initTrace), gen, 0)
      else
        simulateOnceLoop sys params th maxSteps initSt initTrace gen

def runTraceAtSeed {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  (traceIndex : Nat)
  : Option (SimulationResult ρ σ κ × Nat) :=
  let traceSeed := cfg.seed + traceIndex
  let (maybeResult, _, depth) := simulateOnce sys params th (mkStdGen traceSeed) cfg.maxSteps
  maybeResult.map (fun result => (result, depth))

end Veil.ModelChecker.Simulation
