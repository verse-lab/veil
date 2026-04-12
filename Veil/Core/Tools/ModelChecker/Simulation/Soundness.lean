import Veil.Core.Tools.ModelChecker.Simulation.Basic
import Veil.Core.Tools.ModelChecker.Simulation.Path
import Veil.Core.Tools.ModelChecker.Concrete.Core

namespace Veil.ModelChecker.Simulation

def simulationTransitionSystem {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) : RelationalTransitionSystem ρ σ κ where
  assumptions := fun _ => True
  init := fun th st => st ∈ filterInitStatesByConstraints sys params th
  tr := fun th st label st' =>
    (label, ExecutionOutcome.success st') ∈ filterOutcomesByConstraints sys params th st

def StepList.validFromSimulation {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) : StepList σ κ → Bool
  | [] => true
  | step :: steps =>
      (Veil.ModelChecker.Concrete.partitionExecutionOutcome
        (filterOutcomesByConstraints sys params th st)).fst.contains
          (step.transitionLabel, step.nextState)
      && StepList.validFromSimulation sys params th step.nextState steps

theorem StepList.validFromSimulation_sound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) :
  ∀ steps, StepList.validFromSimulation sys params th st steps = true →
    StepList.validFrom (simulationTransitionSystem sys params) th st steps
  | [], _ => by simp [StepList.validFrom]
  | step :: steps, h => by
      have h' :
          (Veil.ModelChecker.Concrete.partitionExecutionOutcome
            (filterOutcomesByConstraints sys params th st)).fst.contains
              (step.transitionLabel, step.nextState) = true ∧
          StepList.validFromSimulation sys params th step.nextState steps = true := by
        simpa [StepList.validFromSimulation, Bool.and_eq_true] using h
      constructor
      · have hmem : (step.transitionLabel, step.nextState) ∈
            (Veil.ModelChecker.Concrete.partitionExecutionOutcome
              (filterOutcomesByConstraints sys params th st)).fst := by
            simpa using h'.1
        exact (Veil.ModelChecker.Concrete.partitionExecutionOutcome.fst_spec _ _ _).mp hmem
      · exact StepList.validFromSimulation_sound sys params th step.nextState steps h'.2

theorem StepList.validFromSimulation_complete {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) :
  ∀ steps, StepList.validFrom (simulationTransitionSystem sys params) th st steps ->
    StepList.validFromSimulation sys params th st steps = true
  | [], _ => by simp [StepList.validFromSimulation]
  | step :: steps, h => by
      rcases h with ⟨hStep, hTail⟩
      have hStep' : (step.transitionLabel, ExecutionOutcome.success step.nextState) ∈
          filterOutcomesByConstraints sys params th st := by
        simpa [simulationTransitionSystem] using hStep
      have hContains : (Veil.ModelChecker.Concrete.partitionExecutionOutcome
          (filterOutcomesByConstraints sys params th st)).fst.contains
            (step.transitionLabel, step.nextState) = true := by
        exact List.elem_eq_true_of_mem <|
          (Veil.ModelChecker.Concrete.partitionExecutionOutcome.fst_spec _ _ _).mpr hStep'
      rw [StepList.validFromSimulation]
      rw [hContains]
      simp [StepList.validFromSimulation_complete sys params th step.nextState steps hTail]

def Trace.isSimulationValidB {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) : Bool :=
  (filterInitStatesByConstraints sys params trace.theory).contains trace.initialState &&
  StepList.validFromSimulation sys params trace.theory trace.initialState trace.steps.toList

abbrev Trace.isSimulationValid {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) : Prop :=
  Trace.isSimulationValidB sys params trace = true

theorem Trace.isSimulationValid_sound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) :
  Trace.isSimulationValid sys params trace → trace.isValid (simulationTransitionSystem sys params) := by
  intro h
  have h' :
      (filterInitStatesByConstraints sys params trace.theory).contains trace.initialState = true ∧
      StepList.validFromSimulation sys params trace.theory trace.initialState trace.steps.toList = true := by
    simpa [Trace.isSimulationValid, Trace.isSimulationValidB, Bool.and_eq_true] using h
  refine {
    theorySatisfiesAssumptions := by simp [simulationTransitionSystem]
    initialStateSatisfiesInit := ?_
    stepsValid := ?_
  }
  · exact by
      have hMem : trace.initialState ∈ filterInitStatesByConstraints sys params trace.theory :=
        List.mem_of_elem_eq_true h'.1
      simpa [simulationTransitionSystem] using hMem
  · simpa [Steps.validFrom] using
      StepList.validFromSimulation_sound sys params trace.theory trace.initialState trace.steps.toList h'.2

theorem Trace.isSimulationValid_complete {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) :
  trace.isValid (simulationTransitionSystem sys params) -> Trace.isSimulationValid sys params trace := by
  intro h
  have hInitMem : trace.initialState ∈ filterInitStatesByConstraints sys params trace.theory := by
    simpa [simulationTransitionSystem] using h.initialStateSatisfiesInit
  have hInit : (filterInitStatesByConstraints sys params trace.theory).contains trace.initialState = true := by
    exact List.elem_eq_true_of_mem hInitMem
  have hSteps : StepList.validFromSimulation sys params trace.theory trace.initialState trace.steps.toList = true := by
    exact StepList.validFromSimulation_complete sys params trace.theory trace.initialState trace.steps.toList (by
      simpa [Steps.validFrom] using h.stepsValid)
  rw [Trace.isSimulationValid, Trace.isSimulationValidB]
  rw [hInit, hSteps]
  simp

theorem pickedTransition_valid {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  [Inhabited (κ × σ)]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (currSt : σ)
  (nexts : List (κ × σ))
  (hNexts : nexts = (Veil.ModelChecker.Concrete.partitionExecutionOutcome
    (filterOutcomesByConstraints sys params th currSt)).fst)
  (hNonempty : nexts ≠ []) (gen : StdGen) :
  let picked := pickNextTransition nexts gen hNonempty
  (simulationTransitionSystem sys params).tr th currSt picked.value.1 picked.value.2 := by
  intro picked
  have hmem : picked.value ∈ nexts := by simpa [picked] using pickNextTransition_mem nexts gen hNonempty
  have hGood : picked.value ∈
      (Veil.ModelChecker.Concrete.partitionExecutionOutcome
        (filterOutcomesByConstraints sys params th currSt)).fst := by
    simpa [hNexts] using hmem
  exact (Veil.ModelChecker.Concrete.partitionExecutionOutcome.fst_spec _ _ _).mp hGood

theorem pickedInitialState_valid {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  [Inhabited σ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ)
  (initStates : List σ)
  (hInitStates : initStates = filterInitStatesByConstraints sys params th)
  (hNonempty : initStates ≠ []) (gen : StdGen) :
  let picked := pickInitialState initStates gen hNonempty
  ({ theory := th, initialState := picked.value, steps := #[] } : Trace ρ σ κ).isValid
    (simulationTransitionSystem sys params) := by
  intro picked
  have hmem : picked.value ∈ initStates := by simpa [picked] using pickInitialState_mem initStates gen hNonempty
  refine Trace.isValid_empty (simulationTransitionSystem sys params) th picked.value ?_ ?_
  · simp [simulationTransitionSystem]
  · simpa [simulationTransitionSystem, hInitStates] using hmem

instance instDecidableTraceIsSimulationValid {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) :
  Decidable (Trace.isSimulationValid sys params trace) := by
  unfold Trace.isSimulationValid
  infer_instance

def Trace.witnessesSimulationViolationB {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) : ViolationKind → Bool
  | .safetyFailure violates =>
      Trace.isSimulationValidB sys params trace &&
      trace.failingStep.isNone &&
      decide (violatedInvariantNames params trace.theory trace.lastState = violates) &&
      !violates.isEmpty
  | .deadlock =>
      Trace.isSimulationValidB sys params trace &&
      trace.failingStep.isNone &&
      !params.terminating.holdsOn trace.theory trace.lastState &&
      let (nexts, _) := Veil.ModelChecker.Concrete.partitionExecutionOutcome
        (filterOutcomesByConstraints sys params trace.theory trace.lastState)
      nexts.isEmpty
  | .assertionFailure exId =>
      match trace.failingStep with
      | some step =>
          Trace.isSimulationValidB sys params trace &&
          (filterOutcomesByConstraints sys params trace.theory trace.lastState).contains
            (step.transitionLabel, ExecutionOutcome.assertionFailure exId step.nextState)
      | none => false

def Trace.witnessesSimulationViolation {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) : ViolationKind → Prop
  | .safetyFailure violates =>
      trace.isValid (simulationTransitionSystem sys params) ∧
      trace.failingStep = none ∧
      violatedInvariantNames params trace.theory trace.lastState = violates ∧
      violates ≠ []
  | .deadlock =>
      trace.isValid (simulationTransitionSystem sys params) ∧
      trace.failingStep = none ∧
      params.terminating.holdsOn trace.theory trace.lastState = false ∧
      let (nexts, _) := Veil.ModelChecker.Concrete.partitionExecutionOutcome
        (filterOutcomesByConstraints sys params trace.theory trace.lastState)
      nexts = []
  | .assertionFailure exId =>
      trace.isValid (simulationTransitionSystem sys params) ∧
      ∃ step,
        trace.failingStep = some step ∧
        (filterOutcomesByConstraints sys params trace.theory trace.lastState).contains
          (step.transitionLabel, ExecutionOutcome.assertionFailure exId step.nextState) = true

theorem Trace.witnessesSimulationViolation_of_check_true {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) (violation : ViolationKind) :
  Trace.witnessesSimulationViolationB sys params trace violation = true →
    Trace.witnessesSimulationViolation sys params trace violation := by
  intro h
  cases violation with
  | safetyFailure violates =>
      have hValid : Trace.isSimulationValidB sys params trace = true := by
        have h' : ((Trace.isSimulationValidB sys params trace = true ∧ trace.failingStep.isNone = true) ∧
            decide (violatedInvariantNames params trace.theory trace.lastState = violates) = true) ∧
            (!violates.isEmpty) = true := by
          simpa [Trace.witnessesSimulationViolationB, Bool.and_eq_true] using h
        exact h'.1.1.1
      refine ⟨Trace.isSimulationValid_sound sys params trace hValid, ?_, ?_, ?_⟩
      · have hNone : trace.failingStep.isNone = true := by
          have h' : ((Trace.isSimulationValidB sys params trace = true ∧ trace.failingStep.isNone = true) ∧
              decide (violatedInvariantNames params trace.theory trace.lastState = violates) = true) ∧
              (!violates.isEmpty) = true := by
            simpa [Trace.witnessesSimulationViolationB, Bool.and_eq_true] using h
          exact h'.1.1.2
        cases hFail : trace.failingStep <;> simp [Option.isNone, hFail] at hNone ⊢
      · have hEq : decide (violatedInvariantNames params trace.theory trace.lastState = violates) = true := by
          have h' : ((Trace.isSimulationValidB sys params trace = true ∧ trace.failingStep.isNone = true) ∧
              decide (violatedInvariantNames params trace.theory trace.lastState = violates) = true) ∧
              (!violates.isEmpty) = true := by
            simpa [Trace.witnessesSimulationViolationB, Bool.and_eq_true] using h
          exact h'.1.2
        simpa [decide_eq_true_eq] using hEq
      · intro hNil
        have h' : (!violates.isEmpty) = true := by
          have hx : ((Trace.isSimulationValidB sys params trace = true ∧ trace.failingStep.isNone = true) ∧
              decide (violatedInvariantNames params trace.theory trace.lastState = violates) = true) ∧
              (!violates.isEmpty) = true := by
            simpa [Trace.witnessesSimulationViolationB, Bool.and_eq_true] using h
          exact hx.2
        simpa [hNil] using h'
  | deadlock =>
      have h' : ((Trace.isSimulationValidB sys params trace = true ∧ trace.failingStep.isNone = true) ∧
          (!params.terminating.holdsOn trace.theory trace.lastState) = true) ∧
          (let (nexts, _) := Veil.ModelChecker.Concrete.partitionExecutionOutcome
            (filterOutcomesByConstraints sys params trace.theory trace.lastState)
           nexts.isEmpty) = true := by
        simpa [Trace.witnessesSimulationViolationB, Bool.and_eq_true] using h
      refine ⟨Trace.isSimulationValid_sound sys params trace h'.1.1.1, ?_, ?_, ?_⟩
      · have hNone : trace.failingStep.isNone = true := h'.1.1.2
        cases hFail : trace.failingStep <;> simp [Option.isNone, hFail] at hNone ⊢
      · simpa using h'.1.2
      · simpa using h'.2
  | assertionFailure exId =>
      cases hFail : trace.failingStep with
      | none => simp [Trace.witnessesSimulationViolationB, hFail] at h
      | some step =>
          have h' : Trace.isSimulationValidB sys params trace = true ∧
              (filterOutcomesByConstraints sys params trace.theory trace.lastState).contains
                (step.transitionLabel, ExecutionOutcome.assertionFailure exId step.nextState) = true := by
            simpa [Trace.witnessesSimulationViolationB, hFail, Bool.and_eq_true] using h
          refine ⟨Trace.isSimulationValid_sound sys params trace h'.1, step, hFail, ?_⟩
          simpa using h'.2

theorem Trace.witnessesSimulationViolation_valid {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) (violation : ViolationKind) :
  Trace.witnessesSimulationViolation sys params trace violation →
    trace.isValid (simulationTransitionSystem sys params) := by
  intro h
  cases violation with
  | safetyFailure _ => exact h.1
  | deadlock => exact h.1
  | assertionFailure _ => exact h.1

noncomputable instance instDecidableTraceWitnessesSimulationViolation {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) (violation : ViolationKind) :
  Decidable (Trace.witnessesSimulationViolation sys params trace violation) := by
  classical
  infer_instance

def ResultSoundB {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (result : ModelCheckingResult ρ σ κ Unit) : Bool :=
  match result with
  | .foundViolation _ violation (some trace) => Trace.witnessesSimulationViolationB sys params trace violation
  | .foundViolation _ _ none => false
  | .noViolationFound _ _ => true
  | .cancelled => true

def ResultSound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (result : ModelCheckingResult ρ σ κ Unit) : Prop :=
  match result with
  | .foundViolation _ violation (some trace) => Trace.witnessesSimulationViolation sys params trace violation
  | .foundViolation _ _ none => False
  | .noViolationFound _ _ => True
  | .cancelled => True

theorem resultSound_of_check_true {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (result : ModelCheckingResult ρ σ κ Unit) :
  ResultSoundB sys params result = true → ResultSound sys params result := by
  intro h
  cases result with
  | foundViolation _ violation traceOpt =>
      cases traceOpt with
      | none => simp [ResultSoundB] at h
      | some trace =>
          simp [ResultSound]
          exact Trace.witnessesSimulationViolation_of_check_true sys params trace violation h
  | noViolationFound _ _ => simp [ResultSound]
  | cancelled => simp [ResultSound]

noncomputable instance instDecidableResultSound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (result : ModelCheckingResult ρ σ κ Unit) :
  Decidable (ResultSound sys params result) := by
  classical
  infer_instance

end Veil.ModelChecker.Simulation
