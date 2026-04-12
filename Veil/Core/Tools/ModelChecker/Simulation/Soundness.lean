import Veil.Core.Tools.ModelChecker.Simulation.Basic
import Veil.Core.Tools.ModelChecker.Simulation.Path
import Veil.Core.Tools.ModelChecker.Concrete.Core

namespace Veil.ModelChecker.Simulation

private instance (priority := high) instBEqTransitionOutcome {σ κ : Type}
  [DecidableEq σ] [DecidableEq κ] : BEq (κ × ExecutionOutcome Int σ) :=
  ⟨fun a b => decide (a = b)⟩

private instance (priority := high) instLawfulBEqTransitionOutcome {σ κ : Type}
  [DecidableEq σ] [DecidableEq κ] : LawfulBEq (κ × ExecutionOutcome Int σ) where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

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
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) : StepList σ κ → Prop
  | [] => True
  | step :: steps =>
      (step.transitionLabel, ExecutionOutcome.success step.nextState) ∈
        filterOutcomesByConstraints sys params th st ∧
      StepList.validFromSimulation sys params th step.nextState steps

theorem StepList.validFromSimulation_sound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) :
  ∀ steps, StepList.validFromSimulation sys params th st steps →
    StepList.validFrom (simulationTransitionSystem sys params) th st steps
  | [], _ => by simp [StepList.validFrom]
  | step :: steps, h => by
      rcases h with ⟨hStep, hTail⟩
      constructor
      · simpa [simulationTransitionSystem] using hStep
      · exact StepList.validFromSimulation_sound sys params th step.nextState steps hTail

theorem StepList.validFromSimulation_complete {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) :
  ∀ steps, StepList.validFrom (simulationTransitionSystem sys params) th st steps ->
    StepList.validFromSimulation sys params th st steps
  | [], _ => by simp [StepList.validFromSimulation]
  | step :: steps, h => by
      rcases h with ⟨hStep, hTail⟩
      constructor
      · simpa [simulationTransitionSystem] using hStep
      · exact StepList.validFromSimulation_complete sys params th step.nextState steps hTail

def Trace.isSimulationValid {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) : Prop :=
  trace.initialState ∈ filterInitStatesByConstraints sys params trace.theory ∧
  StepList.validFromSimulation sys params trace.theory trace.initialState trace.steps.toList

theorem Trace.isSimulationValid_sound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) :
  Trace.isSimulationValid sys params trace → trace.isValid (simulationTransitionSystem sys params) := by
  intro h
  rcases h with ⟨hInit, hSteps⟩
  refine {
    theorySatisfiesAssumptions := by simp [simulationTransitionSystem]
    initialStateSatisfiesInit := ?_
    stepsValid := ?_
  }
  · simpa [simulationTransitionSystem] using hInit
  · simpa [Steps.validFrom] using
      StepList.validFromSimulation_sound sys params trace.theory trace.initialState trace.steps.toList hSteps

theorem Trace.isSimulationValid_complete {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) :
  trace.isValid (simulationTransitionSystem sys params) -> Trace.isSimulationValid sys params trace := by
  intro h
  have hInit : trace.initialState ∈ filterInitStatesByConstraints sys params trace.theory := by
    simpa [simulationTransitionSystem] using h.initialStateSatisfiesInit
  have hSteps : StepList.validFromSimulation sys params trace.theory trace.initialState trace.steps.toList := by
    exact StepList.validFromSimulation_complete sys params trace.theory trace.initialState trace.steps.toList (by
      simpa [Steps.validFrom] using h.stepsValid)
  exact ⟨hInit, hSteps⟩

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

private theorem pushedTrace_valid {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ] [Inhabited (κ × σ)]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (currSt : σ)
  (trace : Trace ρ σ κ)
  (hTheory : trace.theory = th)
  (hValid : trace.isValid (simulationTransitionSystem sys params))
  (hLast : trace.lastState = currSt)
  (hNoFail : trace.failingStep = none)
  (nexts : List (κ × σ))
  (hNexts : nexts = (Veil.ModelChecker.Concrete.partitionExecutionOutcome
    (filterOutcomesByConstraints sys params th currSt)).fst)
  (hNonempty : nexts ≠ [])
  (gen : StdGen) :
  let picked := pickNextTransition nexts gen hNonempty
  let trace' := trace.push { transitionLabel := picked.value.1, nextState := picked.value.2 }
  trace'.isValid (simulationTransitionSystem sys params) ∧
    trace'.theory = th ∧
    trace'.lastState = picked.value.2 ∧
    trace'.failingStep = none := by
  intro picked trace'
  have hRel : (simulationTransitionSystem sys params).tr th currSt picked.value.1 picked.value.2 :=
    pickedTransition_valid sys params th currSt nexts hNexts hNonempty gen
  have hValid' : trace'.isValid (simulationTransitionSystem sys params) := by
    subst hTheory
    exact Trace.push_isValid trace { transitionLabel := picked.value.1, nextState := picked.value.2 }
      (simulationTransitionSystem sys params) hValid (by simpa [hLast] using hRel)
  exact ⟨hValid', by simpa [trace', hTheory], by simp [trace'], by simpa [trace', hNoFail]⟩

private theorem initialTrace_valid {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ] [Inhabited σ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (initStates : List σ)
  (hInitStates : initStates = filterInitStatesByConstraints sys params th)
  (hNonempty : initStates ≠ [])
  (gen : StdGen) :
  let picked := pickInitialState initStates gen hNonempty
  let trace : Trace ρ σ κ := { theory := th, initialState := picked.value, steps := #[] }
  trace.isValid (simulationTransitionSystem sys params) ∧
    trace.theory = th ∧
    trace.lastState = picked.value ∧
    trace.failingStep = none := by
  intro picked trace
  have hValid := pickedInitialState_valid sys params th initStates hInitStates hNonempty gen
  exact ⟨by simpa [trace] using hValid, rfl, by simp [trace], by simp [trace]⟩

instance instDecidableStepListValidFromSimulation {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) (steps : StepList σ κ) :
  Decidable (StepList.validFromSimulation sys params th st steps) := by
  induction steps generalizing st with
  | nil => exact isTrue trivial
  | cons step steps ih =>
      dsimp [StepList.validFromSimulation]
      infer_instance

instance instDecidableTraceIsSimulationValid {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) :
  Decidable (Trace.isSimulationValid sys params trace) := by
  unfold Trace.isSimulationValid
  infer_instance

def Trace.witnessesSimulationViolation {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) : ViolationKind → Prop
  | .safetyFailure violates =>
      Trace.isSimulationValid sys params trace ∧
      trace.failingStep = none ∧
      violatedInvariantNames params trace.theory trace.lastState = violates ∧
      violates ≠ []
  | .deadlock =>
      Trace.isSimulationValid sys params trace ∧
      trace.failingStep = none ∧
      params.terminating.holdsOn trace.theory trace.lastState = false ∧
      let (nexts, _) := Veil.ModelChecker.Concrete.partitionExecutionOutcome
        (filterOutcomesByConstraints sys params trace.theory trace.lastState)
      nexts = []
  | .assertionFailure exId =>
      Trace.isSimulationValid sys params trace ∧
      ∃ step,
        trace.failingStep = some step ∧
        (step.transitionLabel, ExecutionOutcome.assertionFailure exId step.nextState) ∈
          filterOutcomesByConstraints sys params trace.theory trace.lastState

theorem Trace.witnessesSimulationViolation_valid {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) (violation : ViolationKind) :
  Trace.witnessesSimulationViolation sys params trace violation →
    trace.isValid (simulationTransitionSystem sys params) := by
  intro h
  cases violation with
  | safetyFailure _ => exact Trace.isSimulationValid_sound sys params trace h.1
  | deadlock => exact Trace.isSimulationValid_sound sys params trace h.1
  | assertionFailure _ => exact Trace.isSimulationValid_sound sys params trace h.1

noncomputable instance instDecidableTraceWitnessesSimulationViolation {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) (violation : ViolationKind) :
  Decidable (Trace.witnessesSimulationViolation sys params trace violation) := by
  classical
  infer_instance

def ResultSound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (result : ModelCheckingResult ρ σ κ Unit) : Prop :=
  match result with
  | .foundViolation _ violation (some trace) => Trace.witnessesSimulationViolation sys params trace violation
  | .foundViolation _ _ none => False
  | .noViolationFound _ _ => True
  | .cancelled => True

def ResultSoundUnder {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (assumptions : ρ → Prop)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (result : ModelCheckingResult ρ σ κ Unit) : Prop :=
  assumptions th → ResultSound sys params result

theorem simulateOnceLoop_sound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ] [Inhabited (κ × σ)]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (currSt : σ)
  (trace : Trace ρ σ κ)
  (hTheory : trace.theory = th)
  (hValid : trace.isValid (simulationTransitionSystem sys params))
  (hLast : trace.lastState = currSt)
  (hNoFail : trace.failingStep = none) :
  ∀ stepsLeft gen result,
    (simulateOnceLoop sys params th stepsLeft currSt trace gen).1 = some result ->
      ResultSound sys params result := by
  intro stepsLeft
  induction stepsLeft generalizing currSt trace with
  | zero =>
      intro gen result h
      simp [simulateOnceLoop] at h
  | succ steps ih =>
      intro gen result h
      cases hStep : decideAtState sys params th currSt with
      | assertionFailure exId step =>
          simp [simulateOnceLoop, hStep] at h
          cases h
          have hMem : (step.transitionLabel, ExecutionOutcome.assertionFailure exId step.nextState) ∈
              filterOutcomesByConstraints sys params th currSt :=
            decideAtState_assertionFailure_mem sys params th currSt exId step hStep
          let failedTrace := { trace with failingStep := some step }
          have hValidFail : failedTrace.isValid (simulationTransitionSystem sys params) := by
            exact {
              theorySatisfiesAssumptions := hValid.theorySatisfiesAssumptions
              initialStateSatisfiesInit := hValid.initialStateSatisfiesInit
              stepsValid := hValid.stepsValid
            }
          refine ⟨Trace.isSimulationValid_complete sys params failedTrace hValidFail, step, rfl, ?_⟩
          have hLastFail : failedTrace.lastState = currSt := by
            simpa [failedTrace, Trace.lastState] using hLast
          rw [hLastFail]
          simpa [failedTrace, hTheory] using hMem
      | deadlock =>
          simp [simulateOnceLoop, hStep] at h
          cases h
          have hDead := decideAtState_deadlock_spec sys params th currSt hStep
          exact ⟨Trace.isSimulationValid_complete sys params trace hValid, hNoFail,
            by simpa [hTheory, hLast] using hDead.1,
            by simpa [hTheory, hLast] using hDead.2⟩
      | terminated =>
          simp [simulateOnceLoop, hStep] at h
      | «continue» nexts hNonempty =>
          let picked := pickNextTransition nexts gen hNonempty
          let trace' := trace.push { transitionLabel := picked.value.1, nextState := picked.value.2 }
          have hNexts : nexts = (Veil.ModelChecker.Concrete.partitionExecutionOutcome
              (filterOutcomesByConstraints sys params th currSt)).fst :=
            decideAtState_continue_nexts sys params th currSt nexts hNonempty hStep
          have hTrace' := pushedTrace_valid sys params th currSt trace hTheory hValid hLast hNoFail nexts hNexts hNonempty gen
          have hValid' : trace'.isValid (simulationTransitionSystem sys params) := hTrace'.1
          have hTheory' : trace'.theory = th := hTrace'.2.1
          have hNoFail' : trace'.failingStep = none := hTrace'.2.2.2
          have hLast' : trace'.lastState = picked.value.2 := hTrace'.2.2.1
          cases hViol : (violatedInvariantNames params th picked.value.2).isEmpty with
          | true =>
              simp [simulateOnceLoop, hStep, picked, hViol] at h
              exact ih picked.value.2 trace' hTheory' hValid' hLast' hNoFail' picked.gen result h
          | false =>
              simp [simulateOnceLoop, hStep, picked, hViol] at h
              cases h
              have hNonempty : violatedInvariantNames params th picked.value.2 ≠ [] := by
                intro hNil
                simpa [hNil] using hViol
              have hViolEq : violatedInvariantNames params trace'.theory trace'.lastState =
                  violatedInvariantNames params th picked.value.2 := by
                simpa [hTheory', hLast']
              exact ⟨Trace.isSimulationValid_complete sys params trace' hValid', hNoFail', hViolEq, hNonempty⟩

theorem simulateOnce_sound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ] [Inhabited σ] [Inhabited (κ × σ)]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (gen : StdGen) (maxSteps : Nat) (result : ModelCheckingResult ρ σ κ Unit) :
  (simulateOnce sys params th gen maxSteps).1 = some result ->
    ResultSound sys params result := by
  intro h
  unfold simulateOnce at h
  cases hStates : filterInitStatesByConstraints sys params th with
  | nil => simp [hStates] at h
  | cons initSt rest =>
      let picked := pickInitialState (initSt :: rest) gen (by simp)
      let initTrace : Trace ρ σ κ := { theory := th, initialState := picked.value, steps := #[] }
      have hInit := initialTrace_valid sys params th (initSt :: rest) hStates.symm (by simp) gen
      have hValid : initTrace.isValid (simulationTransitionSystem sys params) := hInit.1
      have hLast : initTrace.lastState = picked.value := hInit.2.2.1
      have hNoFail : initTrace.failingStep = none := hInit.2.2.2
      cases hViol : (violatedInvariantNames params th picked.value).isEmpty with
      | true =>
          simp [hStates, picked, hViol] at h
          exact simulateOnceLoop_sound sys params th picked.value initTrace rfl hValid hLast hNoFail maxSteps picked.gen result h
      | false =>
          simp [hStates, picked, hViol] at h
          cases h
          have hNonempty : violatedInvariantNames params th picked.value ≠ [] := by
            intro hNil
            simpa [hNil] using hViol
          exact ⟨Trace.isSimulationValid_complete sys params initTrace hValid, hNoFail, by simpa [hLast], hNonempty⟩

theorem runTraceAtSeed_sound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ] [Inhabited σ] [Inhabited (κ × σ)]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ)
  (th : ρ)
  (cfg : SimulateConfig)
  (traceIndex : Nat)
  (result : ModelCheckingResult ρ σ κ Unit) (depth : Nat) :
  runTraceAtSeed sys params th cfg traceIndex = some (result, depth) ->
    ResultSound sys params result := by
  intro h
  unfold runTraceAtSeed at h
  set traceSeed := cfg.seed + traceIndex
  rcases hSim : simulateOnce sys params th (mkStdGen traceSeed) cfg.maxSteps with ⟨maybeResult, gen', depth'⟩
  simp [traceSeed, hSim] at h
  rcases h with ⟨hSome, rfl⟩
  cases hMaybe : maybeResult with
  | none => simp [hMaybe] at hSome
  | some result' =>
      simp [hMaybe] at hSome
      subst hSome
      have hSimSome : (simulateOnce sys params th (mkStdGen traceSeed) cfg.maxSteps).1 = some result' := by
        simp [hSim, hMaybe]
      exact simulateOnce_sound sys params th (mkStdGen traceSeed) cfg.maxSteps result' hSimSome

noncomputable instance instDecidableResultSound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (result : ModelCheckingResult ρ σ κ Unit) :
  Decidable (ResultSound sys params result) := by
  classical
  infer_instance

noncomputable instance instDecidableResultSoundUnder {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (assumptions : ρ → Prop)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (result : ModelCheckingResult ρ σ κ Unit) :
  Decidable (ResultSoundUnder assumptions sys params th result) := by
  classical
  infer_instance

end Veil.ModelChecker.Simulation
