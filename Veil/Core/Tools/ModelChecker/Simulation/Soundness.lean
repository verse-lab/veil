import Veil.Core.Tools.ModelChecker.Simulation.Basic
import Veil.Core.Tools.ModelChecker.Simulation.Path
import Veil.Core.Tools.ModelChecker.Concrete.Core

namespace Veil.ModelChecker.Simulation

theorem pickedTransition_valid {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (_params : SearchParameters ρ σ) (currSt : σ)
  (nexts : List (κ × σ))
  (hNexts : nexts = (Veil.ModelChecker.Concrete.partitionExecutionOutcome
    (sys.tr th currSt)).fst)
  (selected : κ × σ)
  (hSelected : selected ∈ nexts) :
  sys.toRelational.tr th currSt selected.1 selected.2 := by
  have hGood : selected ∈
      (Veil.ModelChecker.Concrete.partitionExecutionOutcome
        (sys.tr th currSt)).fst := by
    simpa [hNexts] using hSelected
  simpa [EnumerableTransitionSystem.toRelational] using
    (Veil.ModelChecker.Concrete.partitionExecutionOutcome.fst_spec _ _ _).mp hGood

theorem pickedInitialState_valid {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (_params : SearchParameters ρ σ)
  (initStates : List σ)
  (hInitStates : initStates = sys.initStates)
  (selectedInit : σ)
  (hSelected : selectedInit ∈ initStates) :
  ({ theory := th, initialState := selectedInit, steps := #[] } : Trace ρ σ κ).isValid
    sys.toRelational := by
  refine Trace.isValid_empty sys.toRelational th selectedInit ?_ ?_
  · simp [EnumerableTransitionSystem.toRelational]
  · simpa [EnumerableTransitionSystem.toRelational, hInitStates] using hSelected

def Trace.witnessesSimulationViolation {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) : ViolationKind → Prop
  | .assumptionFailure violates =>
      trace.isValid sys.toRelational ∧
      params.violatedAssumptions trace.theory = violates ∧
      violates ≠ []
  | .safetyFailure violates =>
      trace.isValid sys.toRelational ∧
      trace.failingStep = none ∧
      violatedInvariantNames params trace.theory trace.lastState = violates ∧
      violates ≠ []
  | .deadlock =>
      trace.isValid sys.toRelational ∧
      trace.failingStep = none ∧
      (Veil.ModelChecker.Concrete.partitionExecutionOutcome
        (sys.tr trace.theory trace.lastState)).fst = [] ∧
      (Veil.ModelChecker.Concrete.partitionExecutionOutcome
        (sys.tr trace.theory trace.lastState)).snd = [] ∧
      !params.terminating.holdsOn trace.theory trace.lastState = true
  | .assertionFailure exId =>
      trace.isValid sys.toRelational ∧
      ∃ step,
        trace.failingStep = some step ∧
        (step.transitionLabel, ExecutionOutcome.assertionFailure exId step.nextState) ∈
          sys.tr trace.theory trace.lastState

theorem Trace.witnessesSimulationViolation_valid {ρ σ κ : Type} {th : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) (violation : ViolationKind) :
  Trace.witnessesSimulationViolation sys params trace violation →
    trace.isValid sys.toRelational := by
  intro h
  cases violation with
  | assumptionFailure _ => exact h.1
  | safetyFailure _ => exact h.1
  | deadlock => exact h.1
  | assertionFailure _ => exact h.1

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
      cases hPartition : Veil.ModelChecker.Concrete.partitionExecutionOutcome
          (sys.tr th currSt) with
      | mk nexts assertionFailures =>
      cases hFailures : assertionFailures with
      | cons failure failures =>
          rcases failure with ⟨label, exId, st⟩
          simp [simulateOnceLoop, hPartition, hFailures] at h
          cases h
          have hFailureMem : (label, exId, st) ∈
              (Veil.ModelChecker.Concrete.partitionExecutionOutcome
                (sys.tr th currSt)).snd := by
            rw [hPartition]
            simp [hFailures]
          have hMem : (label, ExecutionOutcome.assertionFailure exId st) ∈
              sys.tr th currSt :=
            (Veil.ModelChecker.Concrete.partitionExecutionOutcome.snd_spec _ _ _ _).mp hFailureMem
          let step : Step σ κ := { transitionLabel := label, nextState := st }
          let failedTrace := { trace with failingStep := some step }
          have hValidFail : failedTrace.isValid sys.toRelational := by
            exact {
              theorySatisfiesAssumptions := hValid.theorySatisfiesAssumptions
              initialStateSatisfiesInit := hValid.initialStateSatisfiesInit
              stepsValid := hValid.stepsValid
            }
          refine ⟨hValidFail, step, rfl, ?_⟩
          have hLastFail : failedTrace.lastState = currSt := by
            simpa [failedTrace, Trace.lastState] using hLast
          rw [hLastFail]
          simpa [failedTrace, step, hTheory] using hMem
      | nil =>
          cases hNexts : nexts with
          | nil =>
              cases hTerminating : !params.terminating.holdsOn th currSt with
              | true =>
                  simp [simulateOnceLoop, hPartition, hFailures, hNexts, hTerminating] at h
                  cases h
                  have hNoSuccesses : (Veil.ModelChecker.Concrete.partitionExecutionOutcome
                      (sys.tr trace.theory trace.lastState)).fst = [] := by
                    simp [hTheory, hLast, hPartition, hNexts]
                  have hNoFailures : (Veil.ModelChecker.Concrete.partitionExecutionOutcome
                      (sys.tr trace.theory trace.lastState)).snd = [] := by
                    simp [hTheory, hLast, hPartition, hFailures]
                  have hDeadlock : !params.terminating.holdsOn trace.theory trace.lastState = true := by
                    simpa [hTheory, hLast] using hTerminating
                  exact ⟨hValid, hNoFail, hNoSuccesses, hNoFailures, hDeadlock⟩
              | false =>
                  simp [simulateOnceLoop, hPartition, hFailures, hNexts, hTerminating] at h
          | cons hd tl =>
              let nexts' : List (κ × σ) := hd :: tl
              have hNonempty : nexts' ≠ [] := by simp [nexts']
              let p := randNat gen 0 (nexts'.length - 1)
              let idx := p.1
              let gen' := p.2
              have hlt : idx < nexts'.length := by
                dsimp [idx, p]
                exact randNat_lt_length nexts' hNonempty gen
              let selected := nexts'.get ⟨idx, hlt⟩
              let trace' := trace.push { transitionLabel := selected.1, nextState := selected.2 }
              have hSelected : selected ∈ nexts' := by
                dsimp [selected]
                exact List.get_mem nexts' ⟨idx, hlt⟩
              have hNextsHd : nexts' = (Veil.ModelChecker.Concrete.partitionExecutionOutcome
                  (sys.tr th currSt)).fst := by
                simp [nexts', hPartition, hNexts]
              have hRel : sys.toRelational.tr th currSt selected.1 selected.2 :=
                pickedTransition_valid th sys params currSt nexts' hNextsHd selected hSelected
              have hValid' : trace'.isValid sys.toRelational := by
                exact Trace.push_isValid trace { transitionLabel := selected.1, nextState := selected.2 }
                  sys.toRelational hValid (by simpa [hTheory, hLast] using hRel)
              have hTheory' : trace'.theory = th := by
                simpa [trace', hTheory]
              have hNoFail' : trace'.failingStep = none := by
                simpa [trace', hNoFail]
              have hLast' : trace'.lastState = selected.2 := by
                simp [trace']
              cases hViol : (violatedInvariantNames params th selected.2).isEmpty with
              | true =>
                  have hViolNil : violatedInvariantNames params th selected.2 = [] := by
                    simpa using hViol
                  have hViolNilRaw :
                      violatedInvariantNames params th (hd :: tl)[(randNat gen 0 tl.length).1].2 = [] := by
                    simpa [nexts', p, idx, selected] using hViolNil
                  have hLoop : ((simulateOnceLoop sys params th steps selected.2 trace').run gen').1 = some result := by
                    rw [simulateOnceLoop] at h
                    simp only [hPartition, hFailures, hNexts, StateT.run_bind, Id.instMonad] at h
                    simpa [nexts', p, idx, gen', hlt, selected, trace', hViolNilRaw] using h
                  exact ih selected.2 trace' hTheory' hValid' hLast' hNoFail' gen' result hLoop
              | false =>
                  have hNonempty : violatedInvariantNames params th selected.2 ≠ [] := by
                    intro hNil
                    simp [hNil] at hViol
                  have hNonemptyRaw :
                      violatedInvariantNames params th (hd :: tl)[(randNat gen 0 tl.length).1].2 ≠ [] := by
                    simpa [nexts', p, idx, selected] using hNonempty
                  have hFound : (some (SimulationResult.foundViolation
                      (ViolationKind.safetyFailure (violatedInvariantNames params th selected.2)) trace') :
                      Option (SimulationResult ρ σ κ)) = some result := by
                    rw [simulateOnceLoop] at h
                    simp only [hPartition, hFailures, hNexts, StateT.run_bind, Id.instMonad] at h
                    simpa [nexts', p, idx, gen', hlt, selected, trace', hNonemptyRaw] using h
                  cases hFound
                  have hViolEq : violatedInvariantNames params trace'.theory trace'.lastState =
                      violatedInvariantNames params th selected.2 := by
                    simp [hTheory', hLast']
                  exact ⟨hValid', hNoFail', hViolEq, hNonempty⟩

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
      let initStates : List σ := initSt :: rest
      have hNonempty : initStates ≠ [] := by simp [initStates]
      let p := randNat gen 0 (initStates.length - 1)
      let idx := p.1
      let gen' := p.2
      have hlt : idx < initStates.length := by
        dsimp [idx, p]
        exact randNat_lt_length initStates hNonempty gen
      let selectedInit := initStates.get ⟨idx, hlt⟩
      let initTrace : Trace ρ σ κ := { theory := th, initialState := selectedInit, steps := #[] }
      have hSelectedInit : selectedInit ∈ initStates := by
        dsimp [selectedInit]
        exact List.get_mem initStates ⟨idx, hlt⟩
      have hInitStates : initStates = sys.initStates := by
        simp [initStates, hStates]
      have hValid : initTrace.isValid sys.toRelational := by
        simpa [initTrace] using
          pickedInitialState_valid th sys params initStates hInitStates selectedInit hSelectedInit
      have hLast : initTrace.lastState = selectedInit := by
        simp [initTrace]
      have hNoFail : initTrace.failingStep = none := by
        simp [initTrace]
      cases hViol : (violatedInvariantNames params th selectedInit).isEmpty with
      | true =>
          have hViolNil : violatedInvariantNames params th selectedInit = [] := by
            simpa using hViol
          have hViolNilRaw :
              violatedInvariantNames params th (initSt :: rest)[(randNat gen 0 rest.length).1] = [] := by
            simpa [initStates, p, idx, selectedInit] using hViolNil
          have hLoop : ((simulateOnceLoop sys params th maxSteps selectedInit initTrace).run gen').1 = some result := by
            rw [hStates] at h
            simp only [StateT.run_bind, Id.instMonad] at h
            simpa [initStates, p, idx, gen', hlt, selectedInit, initTrace, hViolNilRaw] using h
          exact simulateOnceLoop_sound th sys params selectedInit initTrace rfl hValid hLast hNoFail maxSteps gen' result hLoop
      | false =>
          have hNonempty : violatedInvariantNames params th selectedInit ≠ [] := by
            intro hNil
            simp [hNil] at hViol
          have hNonemptyRaw :
              violatedInvariantNames params th (initSt :: rest)[(randNat gen 0 rest.length).1] ≠ [] := by
            simpa [initStates, p, idx, selectedInit] using hNonempty
          have hFound : (some (SimulationResult.foundViolation
              (ViolationKind.safetyFailure (violatedInvariantNames params th selectedInit)) initTrace) :
              Option (SimulationResult ρ σ κ)) = some result := by
            rw [hStates] at h
            simp only [StateT.run_bind, Id.instMonad] at h
            simpa [initStates, p, idx, gen', hlt, selectedInit, initTrace, hNonemptyRaw] using h
          cases hFound
          exact ⟨hValid, hNoFail, rfl, hNonempty⟩

/-- Any violation reported by a single indexed random trace is sound. -/
theorem simulateTraceAtIndex_sound {ρ σ κ : Type}
  [DecidableEq σ] [DecidableEq κ] [Inhabited σ] [Inhabited (κ × σ)]
  (th : ρ)
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (cfg : SimulateConfig)
  (traceIndex : Nat)
  (result : SimulationResult ρ σ κ) :
  simulateTraceAtIndex sys params th cfg traceIndex = some result ->
    ReportedViolationSound sys params (some result) := by
  intro h
  unfold simulateTraceAtIndex at h
  set traceSeed := cfg.seed + traceIndex
  have hSimSome : ((simulateOnce sys params th cfg.maxSteps).run (mkStdGen traceSeed)).1 = some result := by
    simpa [traceSeed] using h
  exact simulateOnce_sound th sys params (mkStdGen traceSeed) cfg.maxSteps result hSimSome

end Veil.ModelChecker.Simulation
