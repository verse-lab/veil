import Veil.Core.Tools.ModelChecker.TransitionSystem

namespace Veil.ModelChecker

@[grind]
structure Step (σ : Type) (l : Type) where
  transitionLabel : l
  nextState : σ
deriving Repr, Inhabited

/-- This supports cheap appends. -/
abbrev Steps (σ : Type) (l : Type) := Array (Step σ l)
abbrev StepList (σ : Type) (l : Type) := List (Step σ l)

@[grind =]
def StepList.validFrom [sys : RelationalTransitionSystem ρ σ l] (th : ρ) (st : σ) (steps : StepList σ l) : Prop :=
  match steps with
  | [] => True
  | step :: steps' => sys.tr th st step.transitionLabel step.nextState ∧ validFrom th step.nextState steps'

@[inline, grind]
def Steps.validFrom [sys : RelationalTransitionSystem ρ σ l] (th : ρ) (st : σ) (steps : Steps σ l) : Prop :=
  StepList.validFrom th st steps.toList

@[inline, grind]
def Steps.push (steps : Steps σ l) (step : Step σ l) : Steps σ l := Array.push steps step

@[inline, grind]
def Steps.getLastStateD (steps : Steps σ l) (default : σ) : σ :=
  if let some {nextState := s', ..} := steps.back? then s' else default

@[simp, grind =]
theorem Steps.getLastD_push (steps : Steps σ l) (step : Step σ l) :
  ∀ s, Steps.getLastStateD (Steps.push steps step) s = step.nextState :=
  by simp [Steps.getLastStateD, Steps.push]

@[simp, grind =]
theorem Steps.getLastD_prepend_same (hd : Step σ l) (tl : StepList σ l) (s : σ) :
  Steps.getLastStateD (Array.mk (hd :: tl)) s = Steps.getLastStateD (Array.mk tl) hd.nextState := by grind

@[grind .]
theorem StateTrace.push_validFrom [sys : RelationalTransitionSystem ρ σ l]
  (r : ρ) (s : σ) (ts : Steps σ l) (step : Step σ l) :
  ts.validFrom r s →
  sys.tr r (ts.getLastStateD s) step.transitionLabel step.nextState →
  (ts.push step).validFrom r s := by
  rcases ts with ⟨ts⟩
  simp only [Steps.validFrom, Steps.push, List.push_toArray]
  intro h htr
  induction ts generalizing s with
  | nil => simpa [StepList.validFrom, Steps.getLastStateD]
  | cons hd tl ih => grind

@[grind]
structure Trace (ρ : Type) (σ : Type) (l : Type) where
  theory : ρ
  initialState : σ
  steps : Steps σ l
deriving Repr, Inhabited

@[inline, grind]
def Trace.lastState (trace : Trace ρ σ l) : σ := trace.steps.getLastStateD trace.initialState

@[inline, grind]
def Trace.push (trace : Trace ρ σ l) (step : Step σ l) : Trace ρ σ l :=
  { trace with steps := trace.steps.push step }

@[simp, grind =]
theorem Trace.getLastD_push (trace : Trace ρ σ l) (step : Step σ l) :
  Trace.lastState (Trace.push trace step) = step.nextState :=
  by simp [Trace.lastState, Trace.push]

@[grind]
structure Trace.isValid [sys : RelationalTransitionSystem ρ σ l] (trace : Trace ρ σ l) : Prop where
  theorySatisfiesAssumptions : sys.assumptions (trace.theory)
  initialStateSatisfiesInit : sys.init (trace.theory) (trace.initialState)
  stepsValid : Steps.validFrom trace.theory trace.initialState trace.steps

@[grind .]
theorem Trace.push_isValid [sys : RelationalTransitionSystem ρ σ l] (trace : Trace ρ σ l) (step : Step σ l) :
  trace.isValid →
  sys.tr trace.theory trace.lastState step.transitionLabel step.nextState →
  (trace.push step).isValid := by grind

@[grind .]
theorem Trace.isValid_empty [sys : RelationalTransitionSystem ρ σ l] (th : ρ) (st : σ) :
  sys.assumptions th → sys.init th st →
  ({ theory := th, initialState := st, steps := #[] } : Trace ρ σ l).isValid := by grind

@[simp, grind =]
theorem Trace.getLast_empty (th : ρ) (st : σ) :
  ({ theory := th, initialState := st, steps := #[] } : Trace ρ σ l).lastState = st := by rfl

end Veil.ModelChecker
