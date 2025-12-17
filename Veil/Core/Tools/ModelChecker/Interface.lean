import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.ModelChecker.Trace
import Lean.Data.Json

namespace Veil.ModelChecker
open Lean Trace


structure SafetyProperty (ρ σ : Type) where
  name : Name := Name.anonymous
  property : ρ → σ → Prop
  [decidable : ∀ th st, Decidable (property th st)]

def SafetyProperty.holdsOn (p : SafetyProperty ρ σ) (th : ρ) (st : σ) : Bool :=
  @decide (p.property th st) (p.decidable th st)

instance : Inhabited (SafetyProperty ρ σ) where
  default := {
    name := Name.anonymous
    property := fun _ _ => True
  }

inductive ViolationKind where
  | safetyFailure
  | deadlock
deriving Inhabited, Hashable, BEq, Repr

instance : ToJson ViolationKind where
  toJson
    | .safetyFailure => "safety_failure"
    | .deadlock => "deadlock"

/-- A condition under which the state exploration should be terminated early,
i.e. before full state space is explored. -/
inductive EarlyTerminationCondition where
  | foundViolatingState
  | deadlockOccurred
  | reachedDepthBound (depth : Nat)
deriving Inhabited, Hashable, BEq, Repr

instance : ToJson EarlyTerminationCondition where
  toJson
    | .foundViolatingState => Json.mkObj [("kind", "found_violating_state")]
    | .deadlockOccurred => Json.mkObj [("kind", "deadlock_occurred")]
    | .reachedDepthBound depth => Json.mkObj [("kind", "reached_depth_bound"), ("depth", toJson depth)]

inductive TerminationReason where
  | exploredAllReachableStates
  | earlyTermination (condition : EarlyTerminationCondition)
deriving Inhabited, Hashable, BEq, Repr

instance : ToJson TerminationReason where
  toJson
    | .exploredAllReachableStates => Json.mkObj [("kind", "explored_all_reachable_states")]
    | .earlyTermination condition => Json.mkObj [("kind", "early_termination"), ("condition", toJson condition)]

inductive ModelCheckingResult (ρ σ κ : Type) where
  | foundViolation (violationKind : ViolationKind) (viaTrace : Option (Trace ρ σ κ))
  | noViolationFound (exploredStates : Nat) (terminationReason : TerminationReason)
deriving Inhabited, Repr

instance [ToJson ρ] [ToJson σ] [ToJson κ] : ToJson (ModelCheckingResult ρ σ κ) where
  toJson
    | .foundViolation kind trace => Json.mkObj
        [ ("result", "found_violation"),
          ("violation_kind", toJson kind),
          ("trace", toJson trace) ]
    | .noViolationFound exploredStates reason => Json.mkObj
        [ ("result", "no_violation_found"),
          ("explored_states", toJson exploredStates),
          ("termination_reason", toJson reason) ]

structure SearchParameters (ρ σ : Type) where
  /-- Which property are we trying to find a violation of? (Typically, this is
  the safety property of the system.) -/
  safety : SafetyProperty ρ σ

  /- If a state has no successor states, `terminating` must hold, otherwise a
  deadlock has occurred. -/
  terminating : SafetyProperty ρ σ := default

  /-- Stop the search if _any_ of the stopping conditions are met. Of course,
  the search also terminates if all reachable states have been explored. -/
  earlyTerminationConditions : List EarlyTerminationCondition

class ModelChecker (ts : TransitionSystem ρ σ l) where
  isReachable : SearchParameters ρ σ → ModelCheckingResult ρ σ l

end Veil.ModelChecker
