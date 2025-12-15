import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.ModelChecker.Trace

namespace Veil.ModelChecker
open Lean Trace


structure SafetyProperty (ρ σ : Type) where
  name : Name
  property : ρ → σ → Prop
  [decidable : ∀ th st, Decidable (property th st)]

def SafetyProperty.holdsOn (p : SafetyProperty ρ σ) (th : ρ) (st : σ) : Bool :=
  @decide (p.property th st) (p.decidable th st)


/-- A condition under which the state exploration should be terminated early,
i.e. before full state space is explored. -/
inductive EarlyTerminationCondition where
  | foundViolatingState
  | reachedDepthBound (depth : Nat)
deriving Inhabited, Hashable, BEq, Repr

inductive TerminationReason where
  | exploredAllReachableStates
  | earlyTermination (condition : EarlyTerminationCondition)
deriving Inhabited, Hashable, BEq, Repr

inductive ReachabilityResult (ρ σ κ : Type) where
  | reachable (viaTrace : Option (Trace ρ σ κ))
  | unreachable (exploredStates : Nat) (terminationReason : TerminationReason)
  | unknown
deriving Inhabited, Repr

structure SearchParameters (ρ σ : Type) where
  /-- Which property are we trying to find a violation of? (Typically, this is
  the safety property of the system.) -/
  safety : SafetyProperty ρ σ
  /- If there are no more successor states to explore, `termination` must
  hold, otherwise a deadlock has occurred. -/
  -- termination : SafetyProperty ρ σ

  /-- Stop the search if _any_ of the stopping conditions are met. Of course,
  the search also terminates if all reachable states have been explored. -/
  earlyTerminationConditions : List EarlyTerminationCondition

class ModelChecker (ts : TransitionSystem ρ σ l) where
  isReachable : SearchParameters ρ σ → ReachabilityResult ρ σ l

end Veil.ModelChecker
