import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.ModelChecker.Trace
import Mathlib.Tactic.DeriveFintype
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

/-- Check if the termination reason represents a violation that should prevent handoff. -/
def EarlyTerminationReason.isViolation {σₕ : Type} : EarlyTerminationReason σₕ → Bool
  | .foundViolatingState _ _ | .deadlockOccurred _ | .assertionFailed _ _ => true
  | .reachedDepthBound _ | .cancelled => false

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

/-- Pure function that computes the chunk ranges for splitting a worklist.
Returns a list of (left, right) index pairs representing subarrays. -/
def ParallelConfig.chunkRanges (cfg : ParallelConfig) (totalSize : Nat) : List (Nat × Nat) :=
  if totalSize < cfg.thresholdToParallel then
    [(0, totalSize)]
  else
    let numSubTasks := max 1 cfg.numSubTasks
    let chunkSize := totalSize / numSubTasks
    List.range numSubTasks |>.map fun i =>
      let l := i * chunkSize
      let r := if i == numSubTasks - 1 then totalSize else (i + 1) * chunkSize
      (l, r)

/-- ParallelConfig.chunkRanges produces valid ranges (within bounds). -/
theorem ParallelConfig.chunkRanges_valid (cfg : ParallelConfig) (n : Nat) :
  ∀ lr ∈ cfg.chunkRanges n, lr.1 ≤ lr.2 ∧ lr.2 ≤ n := by
  intro lr h_lr_in
  unfold ParallelConfig.chunkRanges at h_lr_in
  split at h_lr_in
  · simp at h_lr_in
    grind
  · rename_i h_not_small
    simp at h_not_small
    simp [List.mem_map] at h_lr_in
    obtain ⟨i, h_i_in, h_lr_eq⟩ := h_lr_in
    split
    . simp
    . simp
      rename_i h_lr_eq
      apply Nat.div_le_self
    constructor
    . rename_i h_lr_eq
      obtain ⟨a, h_a_lt, h_eq⟩ := h_lr_eq
      rw [← h_eq]
      dsimp
      split_ifs
      · apply Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.lt_of_lt_of_le h_a_lt (le_max_right _ _))))
        rw [Nat.mul_comm]
        apply Nat.div_mul_le_self
      · apply Nat.mul_le_mul_right
        apply Nat.le_succ
    . rename_i h_lr_eq
      obtain ⟨a, h_a_lt, h_eq⟩ := h_lr_eq
      rw [← h_eq]; dsimp
      split_ifs <;> try apply Nat.le_refl
      trans (max 1 cfg.numSubTasks) * (n / max 1 cfg.numSubTasks)
      · apply Nat.mul_le_mul_right; omega
      · rw [Nat.mul_comm]; apply Nat.div_mul_le_self


/-- ParallelConfig.chunkRanges covers all indices. -/
theorem ParallelConfig.chunkRanges_cover (cfg : ParallelConfig) (n : Nat) :
  ∀ i, i < n → ∃ lr ∈ cfg.chunkRanges n, lr.1 ≤ i ∧ i < lr.2 := by
  intro i h_i_lt
  unfold ParallelConfig.chunkRanges
  split
  · exists (0, n)
    simp
    omega
  · rename_i h_not_small
    let k := max 1 cfg.numSubTasks
    let s := n / k
    have hk_pos : 0 < k := Nat.le_max_left 1 _
    let idx := if i < (k - 1) * s then i / s else k - 1
    let l := idx * s
    let r := if idx == k - 1 then n else (idx + 1) * s
    exists (l, r)
    constructor
    · apply List.mem_map_of_mem
      rw [List.mem_range]
      dsimp [idx]
      split_ifs with h_cond
      · have hs_pos : 0 < s := Nat.pos_of_ne_zero (fun h => by simp [h] at h_cond)
        calc
          i / s < k - 1 := Nat.div_lt_of_lt_mul (by grind)
          _     < k     := Nat.pred_lt (by grind)
      · apply Nat.pred_lt (by grind)
    . simp
      constructor
      . dsimp [l, idx]
        split_ifs with h_cond
        . exact Nat.div_mul_le_self i s
        . omega
      . dsimp [r]
        split_ifs with h_is_last
        . exact h_i_lt
        . simp [idx] at h_is_last
          have h_idx_val : idx = i / s := by
            dsimp [idx]; split_ifs; rfl; grind
          rw [h_idx_val]
          rw [Nat.add_mul]
          rw [Nat.one_mul]
          apply Nat.lt_div_mul_add
          refine Nat.pos_of_ne_zero (fun h_s_zero => ?_)
          have h_lt := h_is_last.1
          rw [h_s_zero, Nat.mul_zero] at h_lt
          exact Nat.not_lt_zero i h_lt


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
