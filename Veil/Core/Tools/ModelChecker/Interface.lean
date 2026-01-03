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
  | safetyFailure (violates : List Name)
  | deadlock
  /-- An assertion (require/assert) in the code failed during execution. -/
  | assertionFailure (exceptionId : Int)
deriving Inhabited, Hashable, BEq, Repr

instance : ToJson ViolationKind where
  toJson
    | .safetyFailure violates => Json.mkObj [("kind", "safety_failure"), ("violates", toJson violates)]
    | .deadlock => Json.mkObj [("kind", "deadlock")]
    | .assertionFailure exId => Json.mkObj [("kind", "assertion_failure"), ("exception_id", toJson exId)]

inductive EarlyTerminationCondition where
  | foundViolatingState
  | deadlockOccurred
  | assertionFailed
  | reachedDepthBound (depth : Nat)
  | cancelled
deriving Inhabited, Hashable, BEq, Repr

/-- A condition under which the state exploration should be terminated early,
i.e. before full state space is explored. -/
inductive EarlyTerminationReason (σₕ : Type) where
  | foundViolatingState (fp : σₕ) (violates : List Name)
  | deadlockOccurred (fp : σₕ)
  | assertionFailed (fp : σₕ) (exceptionId : Int)
  | reachedDepthBound (depth : Nat)
  | cancelled
deriving Inhabited, Hashable, BEq, Repr

instance [ToJson σₕ] : ToJson (EarlyTerminationReason σₕ) where
  toJson
    | .foundViolatingState fp violates => Json.mkObj [("kind", "found_violating_state"), ("state_fingerprint", toJson fp), ("violates", toJson violates)]
    | .deadlockOccurred fp => Json.mkObj [("kind", "deadlock_occurred"), ("state_fingerprint", toJson fp)]
    | .assertionFailed fp exId => Json.mkObj [("kind", "assertion_failed"), ("state_fingerprint", toJson fp), ("exception_id", toJson exId)]
    | .reachedDepthBound depth => Json.mkObj [("kind", "reached_depth_bound"), ("depth", toJson depth)]
    | .cancelled => Json.mkObj [("kind", "cancelled")]

inductive TerminationReason (σₕ : Type) where
  | exploredAllReachableStates
  | earlyTermination (condition : EarlyTerminationReason σₕ)
deriving Inhabited, Hashable, BEq, Repr

instance [ToJson σₕ] : ToJson (TerminationReason σₕ) where
  toJson
    | .exploredAllReachableStates => Json.mkObj [("kind", "explored_all_reachable_states")]
    | .earlyTermination condition => Json.mkObj [("kind", "early_termination"), ("condition", toJson condition)]

inductive ModelCheckingResult (ρ σ κ σₕ : Type) where
  | foundViolation (fp : σₕ) (violation : ViolationKind) (viaTrace : Option (Trace ρ σ κ))
  | noViolationFound (exploredStates : Nat) (terminationReason : TerminationReason σₕ)
  | cancelled
deriving Inhabited, Repr

instance [ToJson ρ] [ToJson σ] [ToJson κ] [ToJson σₕ] : ToJson (ModelCheckingResult ρ σ κ σₕ) where
  toJson
    | .foundViolation fp violation trace => Json.mkObj
        [ ("result", "found_violation"),
          ("violation", toJson violation),
          ("trace", toJson trace),
          ("state_fingerprint", toJson fp) ]
    | .noViolationFound exploredStates reason => Json.mkObj
        [ ("result", "no_violation_found"),
          ("explored_states", toJson exploredStates),
          ("termination_reason", toJson reason) ]
    | .cancelled => Json.mkObj [("result", "cancelled")]

structure ParallelConfig where
  /-- Number of sub-tasks to split the worklist into. -/
  numSubTasks : Nat := 4
  /-- Threshold of worklist size to start parallel processing.
  If the worklist size is below this threshold, sequential processing
  is used. -/
  thresholdToParallel : Nat := 20
deriving Inhabited, Repr

instance ParallelConfig.hasQuote : Quote ParallelConfig `term where
  quote cfg :=
    Syntax.mkCApp ``ParallelConfig.mk
      #[Syntax.mkNumLit (toString cfg.numSubTasks),
        Syntax.mkNumLit (toString cfg.thresholdToParallel)]

def ParallelConfig.taskSplit (cfg : ParallelConfig) (f : Array α → IO β) (worklist : Array α)
  : IO (List (Task (Except IO.Error β))) := do
  if worklist.size < cfg.thresholdToParallel then
    return [← IO.asTask (f worklist)]
  else
    let numSubTasks := max 1 cfg.numSubTasks
    let chunkSize := worklist.size / numSubTasks
    List.range numSubTasks |>.mapM fun i => do
      let l := i * chunkSize
      let r := if i == numSubTasks - 1 then worklist.size else (i + 1) * chunkSize
      IO.asTask (f (worklist.toSubarray l r))

structure SearchParameters (ρ σ : Type) where
  /-- Which properties are we trying to find a violation of? (Typically, this
  list contains all the safety properties and invariants of the system.) -/
  invariants : List (SafetyProperty ρ σ)

  /- If a state has no successor states, `terminating` must hold, otherwise a
  deadlock has occurred. -/
  terminating : SafetyProperty ρ σ := default

  /-- Stop the search if _any_ of the stopping conditions are met. Of course,
  the search also terminates if all reachable states have been explored. -/
  earlyTerminationConditions : List EarlyTerminationCondition

class ModelChecker (ts : TransitionSystem ρ σ l) where
  isReachable : SearchParameters ρ σ → Option ParallelConfig → ModelCheckingResult ρ σ l σₕ

end Veil.ModelChecker
