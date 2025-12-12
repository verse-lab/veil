import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.ModelChecker.Trace

namespace Veil.ModelChecker
open Lean Trace


structure SafetyProperty (ρ σ : Type) where
  name : Name
  property : ρ → σ → Prop
  decidable : ∀ th st, Decidable (property th st)

def SafetyProperty.holdsOn (p : SafetyProperty ρ σ) (th : ρ) (st : σ) : Bool :=
  @decide (p.property th st) (p.decidable th st)

inductive ReachabilityResult where
  | reachable (viaTrace : Option (Trace ρ σ l))
  | unreachable
  | unknown
deriving Inhabited

inductive StoppingCondition where
  | exploredAllReachableStates
  | foundViolatingState
  -- | reachedDepthBound (depth : Nat)
deriving Inhabited, Hashable, BEq

structure SearchParameters (ρ σ : Type) where
  /-- Which property are we trying to find a violation of? (Typically, this is
  the safety property of the system.) -/
  safety : SafetyProperty ρ σ
  /- If there are no more successor states to explore, `termination` must
  hold, otherwise a deadlock has occurred. -/
  -- termination : SafetyProperty ρ σ
  /-- Stop the search if _any_ of the stopping conditions are met. -/
  stoppingConditions : List StoppingCondition

class ModelChecker (ts : TransitionSystem ρ σ l) where
  isReachable : SearchParameters ρ σ → ReachabilityResult

end Veil.ModelChecker
