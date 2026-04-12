import Veil.Core.Tools.ModelChecker.Simulation.Basic
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
      (filterOutcomesByConstraints sys params th st).any fun (label, outcome) =>
        match outcome with
        | .success st' => label == step.transitionLabel && st' == step.nextState
        | _ => false
      && StepList.validFromSimulation sys params th step.nextState steps

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

abbrev Trace.witnessesSimulationViolation {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (trace : Trace ρ σ κ) (violation : ViolationKind) : Prop :=
  Trace.witnessesSimulationViolationB sys params trace violation = true

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
  ResultSoundB sys params result = true

instance instDecidableResultSound {ρ σ κ : Type} {th₀ : ρ}
  [DecidableEq σ] [DecidableEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (result : ModelCheckingResult ρ σ κ Unit) :
  Decidable (ResultSound sys params result) := by
  unfold ResultSound
  infer_instance

end Veil.ModelChecker.Simulation
