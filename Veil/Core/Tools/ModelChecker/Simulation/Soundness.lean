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

def StepList.validFromSimulation {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) : StepList σ κ → Prop
  | [] => True
  | step :: steps =>
      (step.transitionLabel, ExecutionOutcome.success step.nextState) ∈
        sys.tr th st ∧
      StepList.validFromSimulation sys params th step.nextState steps

theorem StepList.validFromSimulation_sound {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ) (st : σ) :
  ∀ steps, StepList.validFromSimulation sys params th st steps →
    StepList.validFrom sys.toRelational th st steps
  | [], _ => by simp [StepList.validFrom]
  | step :: steps, h => by
      rcases h with ⟨hStep, hTail⟩
      constructor
      · simpa [EnumerableTransitionSystem.toRelational] using hStep
      · exact StepList.validFromSimulation_sound th sys params step.nextState steps hTail

theorem StepList.validFromSimulation_complete {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ) (st : σ) :
  ∀ steps, StepList.validFrom sys.toRelational th st steps ->
    StepList.validFromSimulation sys params th st steps
  | [], _ => by simp [StepList.validFromSimulation]
  | step :: steps, h => by
      rcases h with ⟨hStep, hTail⟩
      constructor
      · simpa [EnumerableTransitionSystem.toRelational] using hStep
      · exact StepList.validFromSimulation_complete th sys params step.nextState steps hTail

def Trace.isSimulationValid {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) : Prop :=
  trace.initialState ∈ sys.initStates ∧
  StepList.validFromSimulation sys params trace.theory trace.initialState trace.steps.toList

theorem Trace.isSimulationValid_sound {ρ σ κ : Type} {th : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) (hTheory : trace.theory = th) :
  Trace.isSimulationValid sys params trace → trace.isValid sys.toRelational := by
  subst th
  intro h
  rcases h with ⟨hInit, hSteps⟩
  refine {
    theorySatisfiesAssumptions := by simp [EnumerableTransitionSystem.toRelational]
    initialStateSatisfiesInit := ?_
    stepsValid := ?_
  }
  · simpa [EnumerableTransitionSystem.toRelational] using hInit
  · simpa [Steps.validFrom] using
      StepList.validFromSimulation_sound trace.theory sys params trace.initialState trace.steps.toList hSteps

theorem Trace.isSimulationValid_complete {ρ σ κ : Type} {th : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) (hTheory : trace.theory = th) :
  trace.isValid sys.toRelational -> Trace.isSimulationValid sys params trace := by
  subst th
  intro h
  have hInit : trace.initialState ∈ sys.initStates := by
    simpa [EnumerableTransitionSystem.toRelational] using h.initialStateSatisfiesInit
  have hSteps : StepList.validFromSimulation sys params trace.theory trace.initialState trace.steps.toList := by
    exact StepList.validFromSimulation_complete trace.theory sys params trace.initialState trace.steps.toList (by
      simpa [Steps.validFrom] using h.stepsValid)
  exact ⟨hInit, hSteps⟩

theorem pickedTransition_valid {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ]
  [Inhabited (κ × σ)]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (_params : SearchParameters ρ σ) (currSt : σ)
  (nexts : List (κ × σ))
  (hNexts : nexts = (Veil.ModelChecker.Concrete.partitionExecutionOutcome
    (sys.tr th currSt)).fst)
  (hNonempty : nexts ≠ []) (gen : StdGen) :
  let picked := (pickNextTransition nexts hNonempty).run gen
  sys.toRelational.tr th currSt picked.1.value.1 picked.1.value.2 := by
  intro picked
  have hmem : picked.1.value ∈ nexts := by simpa [picked] using pickNextTransition_mem nexts gen hNonempty
  have hGood : picked.1.value ∈
      (Veil.ModelChecker.Concrete.partitionExecutionOutcome
        (sys.tr th currSt)).fst := by
    simpa [hNexts] using hmem
  simpa [EnumerableTransitionSystem.toRelational] using
    (Veil.ModelChecker.Concrete.partitionExecutionOutcome.fst_spec _ _ _).mp hGood

theorem pickedInitialState_valid {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ]
  [Inhabited σ]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (_params : SearchParameters ρ σ)
  (initStates : List σ)
  (hInitStates : initStates = sys.initStates)
  (hNonempty : initStates ≠ []) (gen : StdGen) :
  let picked := (pickInitialState initStates hNonempty).run gen
  ({ theory := th, initialState := picked.1.value, steps := #[] } : Trace ρ σ κ).isValid
    sys.toRelational := by
  intro picked
  have hmem : picked.1.value ∈ initStates := by simpa [picked] using pickInitialState_mem initStates gen hNonempty
  refine Trace.isValid_empty sys.toRelational th picked.1.value ?_ ?_
  · simp [EnumerableTransitionSystem.toRelational]
  · simpa [EnumerableTransitionSystem.toRelational, hInitStates] using hmem

private theorem pushedTrace_valid {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ] [Inhabited (κ × σ)]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (currSt : σ)
  (trace : Trace ρ σ κ)
  (hTheory : trace.theory = th)
  (hValid : trace.isValid sys.toRelational)
  (hLast : trace.lastState = currSt)
  (hNoFail : trace.failingStep = none)
  (nexts : List (κ × σ))
  (hNexts : nexts = (Veil.ModelChecker.Concrete.partitionExecutionOutcome
    (sys.tr th currSt)).fst)
  (hNonempty : nexts ≠ [])
  (gen : StdGen) :
  let picked := (pickNextTransition nexts hNonempty).run gen
  let trace' := trace.push { transitionLabel := picked.1.value.1, nextState := picked.1.value.2 }
  trace'.isValid sys.toRelational ∧
    trace'.theory = th ∧
    trace'.lastState = picked.1.value.2 ∧
    trace'.failingStep = none := by
  intro picked trace'
  have hRel : sys.toRelational.tr th currSt picked.1.value.1 picked.1.value.2 :=
    pickedTransition_valid th sys params currSt nexts hNexts hNonempty gen
  have hValid' : trace'.isValid sys.toRelational := by
    exact Trace.push_isValid trace { transitionLabel := picked.1.value.1, nextState := picked.1.value.2 }
      sys.toRelational hValid (by simpa [hTheory, hLast] using hRel)
  exact ⟨hValid', by simpa [trace', hTheory], by simp [trace'], by simpa [trace', hNoFail]⟩

private theorem initialTrace_valid {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ] [Inhabited σ]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (initStates : List σ)
  (hInitStates : initStates = sys.initStates)
  (hNonempty : initStates ≠ [])
  (gen : StdGen) :
  let picked := (pickInitialState initStates hNonempty).run gen
  let trace : Trace ρ σ κ := { theory := th, initialState := picked.1.value, steps := #[] }
  trace.isValid sys.toRelational ∧
    trace.theory = th ∧
    trace.lastState = picked.1.value ∧
  trace.failingStep = none := by
  intro picked trace
  have hValid := pickedInitialState_valid th sys params initStates hInitStates hNonempty gen
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
  | .assumptionFailure violates =>
      Trace.isSimulationValid sys params trace ∧
      params.violatedAssumptions trace.theory = violates ∧
      violates ≠ []
  | .safetyFailure violates =>
      Trace.isSimulationValid sys params trace ∧
      trace.failingStep = none ∧
      violatedInvariantNames params trace.theory trace.lastState = violates ∧
      violates ≠ []
  | .deadlock =>
      Trace.isSimulationValid sys params trace ∧
      trace.failingStep = none ∧
      decideAtState sys params trace.theory trace.lastState = .deadlock
  | .assertionFailure exId =>
      Trace.isSimulationValid sys params trace ∧
      ∃ step,
        trace.failingStep = some step ∧
        (step.transitionLabel, ExecutionOutcome.assertionFailure exId step.nextState) ∈
          sys.tr trace.theory trace.lastState

theorem Trace.witnessesSimulationViolation_valid {ρ σ κ : Type} {th : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) (violation : ViolationKind)
  (hTheory : trace.theory = th) :
  Trace.witnessesSimulationViolation sys params trace violation →
    trace.isValid sys.toRelational := by
  intro h
  cases violation with
  | assumptionFailure _ => exact Trace.isSimulationValid_sound sys params trace hTheory h.1
  | safetyFailure _ => exact Trace.isSimulationValid_sound sys params trace hTheory h.1
  | deadlock => exact Trace.isSimulationValid_sound sys params trace hTheory h.1
  | assertionFailure _ => exact Trace.isSimulationValid_sound sys params trace hTheory h.1

def ReportedViolationSound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (result : Option (SimulationResult ρ σ κ)) : Prop :=
  match result with
  | some (.foundViolation violation trace) => Trace.witnessesSimulationViolation sys params trace violation
  | some .cancelled => True
  | none => True

theorem simulateOnceLoop_sound {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ] [Inhabited (κ × σ)]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (currSt : σ)
  (trace : Trace ρ σ κ)
  (hTheory : trace.theory = th)
  (hValid : trace.isValid sys.toRelational)
  (hLast : trace.lastState = currSt)
  (hNoFail : trace.failingStep = none) :
  ∀ stepsLeft gen result,
    ((simulateOnceLoop sys params th stepsLeft currSt trace).run gen).1 = some result ->
      ReportedViolationSound sys params (some result) := by
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
              sys.tr th currSt :=
            decideAtState_assertionFailure_mem sys params th currSt exId step hStep
          let failedTrace := { trace with failingStep := some step }
          have hValidFail : failedTrace.isValid sys.toRelational := by
            exact {
              theorySatisfiesAssumptions := hValid.theorySatisfiesAssumptions
              initialStateSatisfiesInit := hValid.initialStateSatisfiesInit
              stepsValid := hValid.stepsValid
            }
          refine ⟨Trace.isSimulationValid_complete sys params failedTrace (by simp [failedTrace, hTheory]) hValidFail, step, rfl, ?_⟩
          have hLastFail : failedTrace.lastState = currSt := by
            simpa [failedTrace, Trace.lastState] using hLast
          rw [hLastFail]
          simpa [failedTrace, hTheory] using hMem
      | deadlock =>
          simp [simulateOnceLoop, hStep] at h
          cases h
          exact ⟨Trace.isSimulationValid_complete sys params trace hTheory hValid, hNoFail,
            by simpa [hTheory, hLast] using hStep⟩
      | terminated =>
          simp [simulateOnceLoop, hStep] at h
      | «continue» nexts hNonempty =>
          rcases hPick : (pickNextTransition nexts hNonempty).run gen with ⟨picked, gen'⟩
          let trace' := trace.push { transitionLabel := picked.value.1, nextState := picked.value.2 }
          have hNexts : nexts = (Veil.ModelChecker.Concrete.partitionExecutionOutcome
              (sys.tr th currSt)).fst :=
            decideAtState_continue_nexts sys params th currSt nexts hNonempty hStep
          have hTrace' := pushedTrace_valid th sys params currSt trace hTheory hValid hLast hNoFail nexts hNexts hNonempty gen
          have hValid' : trace'.isValid sys.toRelational := by
            simpa [hPick, trace'] using hTrace'.1
          have hTheory' : trace'.theory = th := by
            simpa [hPick, trace'] using hTrace'.2.1
          have hNoFail' : trace'.failingStep = none := by
            simpa [hPick, trace'] using hTrace'.2.2.2
          have hLast' : trace'.lastState = picked.value.2 := by
            simp [trace']
          cases hViol : (violatedInvariantNames params th picked.value.2).isEmpty with
          | true =>
              have hLoop : ((simulateOnceLoop sys params th steps picked.value.2 trace').run gen').1 = some result := by
                rw [simulateOnceLoop, hStep] at h
                simp only [StateT.run_bind, hPick, Id.instMonad] at h
                simpa [trace', hViol] using h
              exact ih picked.value.2 trace' hTheory' hValid' hLast' hNoFail' gen' result hLoop
          | false =>
              have hFound : (some (SimulationResult.foundViolation
                  (ViolationKind.safetyFailure (violatedInvariantNames params th picked.value.2)) trace') :
                  Option (SimulationResult ρ σ κ)) = some result := by
                rw [simulateOnceLoop, hStep] at h
                simp only [StateT.run_bind, hPick, Id.instMonad] at h
                simpa [trace', hViol] using h
              cases hFound
              have hNonempty : violatedInvariantNames params th picked.value.2 ≠ [] := by
                intro hNil
                simp [hNil] at hViol
              have hViolEq : violatedInvariantNames params trace'.theory trace'.lastState =
                  violatedInvariantNames params th picked.value.2 := by
                simp [hTheory', hLast']
              exact ⟨Trace.isSimulationValid_complete sys params trace' hTheory' hValid', hNoFail', hViolEq, hNonempty⟩

theorem simulateOnce_sound {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ] [Inhabited σ] [Inhabited (κ × σ)]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ) (gen : StdGen) (maxSteps : Nat) (result : SimulationResult ρ σ κ) :
  ((simulateOnce sys params th maxSteps).run gen).1 = some result ->
    ReportedViolationSound sys params (some result) := by
  intro h
  unfold simulateOnce at h
  cases hStates : sys.initStates with
  | nil => simp [hStates] at h
  | cons initSt rest =>
      rcases hPick : (pickInitialState (initSt :: rest) (by simp)).run gen with ⟨picked, gen'⟩
      let initTrace : Trace ρ σ κ := { theory := th, initialState := picked.value, steps := #[] }
      have hInit := initialTrace_valid th sys params (initSt :: rest) hStates.symm (by simp) gen
      have hValid : initTrace.isValid sys.toRelational := by
        simpa [hPick, initTrace] using hInit.1
      have hLast : initTrace.lastState = picked.value := by
        simp [initTrace]
      have hNoFail : initTrace.failingStep = none := by
        simp [initTrace]
      cases hViol : (violatedInvariantNames params th picked.value).isEmpty with
      | true =>
          have hLoop : ((simulateOnceLoop sys params th maxSteps picked.value initTrace).run gen').1 = some result := by
            rw [hStates] at h
            simp only [StateT.run_bind, hPick, Id.instMonad] at h
            simpa [initTrace, hViol] using h
          exact simulateOnceLoop_sound th sys params picked.value initTrace rfl hValid hLast hNoFail maxSteps gen' result hLoop
      | false =>
          have hFound : (some (SimulationResult.foundViolation
              (ViolationKind.safetyFailure (violatedInvariantNames params th picked.value)) initTrace) :
              Option (SimulationResult ρ σ κ)) = some result := by
            rw [hStates] at h
            simp only [StateT.run_bind, hPick, Id.instMonad] at h
            simpa [initTrace, hViol] using h
          cases hFound
          have hNonempty : violatedInvariantNames params th picked.value ≠ [] := by
            intro hNil
            simp [hNil] at hViol
          exact ⟨Trace.isSimulationValid_complete sys params initTrace rfl hValid, hNoFail, rfl, hNonempty⟩

theorem runTraceAtSeed_sound {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ] [Inhabited σ] [Inhabited (κ × σ)]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (cfg : SimulateConfig)
  (traceIndex : Nat)
  (result : SimulationResult ρ σ κ) (depth : Nat) :
  runTraceAtSeed sys params th cfg traceIndex = some (result, depth) ->
    ReportedViolationSound sys params (some result) := by
  intro h
  unfold runTraceAtSeed at h
  set traceSeed := cfg.seed + traceIndex
  rcases hSim : (simulateOnce sys params th cfg.maxSteps).run (mkStdGen traceSeed) with ⟨maybeResult, gen'⟩
  simp [traceSeed, hSim] at h
  rcases h with ⟨hSome, rfl⟩
  cases hMaybe : maybeResult with
  | none => simp [hMaybe] at hSome
  | some result' =>
      simp [hMaybe] at hSome
      subst hSome
      have hSimSome : ((simulateOnce sys params th cfg.maxSteps).run (mkStdGen traceSeed)).1 = some result' := by
        simp [hSim, hMaybe]
      exact simulateOnce_sound th sys params (mkStdGen traceSeed) cfg.maxSteps result' hSimSome

end Veil.ModelChecker.Simulation
