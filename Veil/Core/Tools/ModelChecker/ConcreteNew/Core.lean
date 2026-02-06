import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.ModelChecker.Interface
import Veil.Core.Tools.ModelChecker.Trace

namespace Veil.ModelChecker.Concrete
open Std

/-- A function that maps a full state to a view of the state. -/
class StateView (FullState View : Type) where
  view : FullState → View

class abbrev StateFingerprint (FullState View : Type)
  := BEq View, LawfulBEq View, Hashable View, LawfulHashable View, StateView FullState View

-- NOTE: Without setting these, Lean might get stuck when synthesizing
-- `BEq` or `Hashable` instances in scenarios that are completely irrelevant
-- to `StateFingerprint`
attribute [instance low] StateFingerprint.toBEq StateFingerprint.toLawfulBEq StateFingerprint.toHashable StateFingerprint.toLawfulHashable StateFingerprint.toStateView

instance StateFingerprint.ofHash (σ : Type) [Hashable σ] : StateFingerprint σ UInt64 where
  beq := BEq.beq
  rfl := BEq.rfl
  eq_of_beq := LawfulBEq.eq_of_beq
  hash_eq := LawfulHashable.hash_eq
  view := hash

structure QueueItem (σₕ σ : Type) where
  fingerprint : σₕ
  state : σ
  depth : Nat
deriving BEq, DecidableEq, Repr

structure ActionStat where
  statesGenerated : Nat
  distinctStates : Nat
deriving Lean.ToJson, Lean.FromJson, BEq, DecidableEq, Repr, Inhabited

/-- A model checker search context is parametrised by the system that's being
checked and the theory it's being checked under. -/
structure BaseSearchContext (σ κ σₕ : Type)
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
where
  seen  : Std.HashSet σₕ
  /- We use a `HashMap σ_post (σ_pre × κ)` to store the log of transitions, which
  will make it easier to reconstruct counterexample trace. -/
  log                : Std.HashMap σₕ (σₕ × κ)
  violatingStates    : List (σₕ × ViolationKind)
  /-- Have we finished the search? If so, why? -/
  finished           : Option (TerminationReason σₕ)
  /-- The depth up to which ALL states have been fully explored (successors enqueued) -/
  completedDepth     : Nat
  /-- The depth of the current BFS frontier being processed -/
  currentFrontierDepth : Nat
  /-- Total number of post-states generated (before deduplication) -/
  statesFound : Nat
  /-- Per-action statistics: label → stats -/
  actionStatsMap : Std.HashMap κ ActionStat

structure SearchContextInvariants {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  -- NOTE: Although `params` is not used in the invariants below yet,
  -- we should better keep it here for future extensions.
  (params : SearchParameters ρ σ)
  (inQueue : QueueItem σₕ σ → Prop)
  (seen : σₕ → Prop) : Prop
where
  queue_sound        : ∀ x st d, inQueue ⟨x, st, d⟩ → sys.reachable st ∧ seen x ∧ x = fp.view st
  visited_sound      : Function.Injective fp.view → ∀ x, seen (fp.view x) → sys.reachable x

variable {ρ σ κ σₕ : Type} [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ]
  (params : SearchParameters ρ σ) (th : ρ) (fpSt : σₕ) (curr : σ)

@[inline]
def BaseSearchContext.hasFinished (ctx : BaseSearchContext σ κ σₕ) : Bool := ctx.finished.isSome

-- @[inline]
def BaseSearchContext.initial (initialStates : List σ) : BaseSearchContext σ κ σₕ :=
  let initStates := initialStates.map fp.view
  {
    seen := HashSet.ofList initStates,
    log := Std.HashMap.emptyWithCapacity,
    violatingStates := [],
    finished := none,
    completedDepth := 0,
    currentFrontierDepth := 0,
    statesFound := initStates.length,
    actionStatsMap := {}
  }

-- NOTE: Hopefully, if `outcomes` does not have any other reference, then
-- Lean should be able to reuse constructors inside it? Can we somehow
-- achieve zero additional memory allocation here?

/-- Partition a list of `(label × ExecutionOutcome)` pairs into two components:
a list of successful transitions, and a list of transitions where exceptions
were raised. The divergence part is discarded. -/
def partitionExecutionOutcome (outcomes : List (κ × ExecutionOutcome Int σ)) :
  List (κ × σ) × List (Int × σ) :=
  outcomes.foldr
    (init := ([], []))
    (fun (label, outcome) (succs, exns) =>
      match outcome with
      | .success st => ((label, st) :: succs, exns)
      | .assertionFailure exId st => (succs, (exId, st) :: exns)
      | .divergence => (succs, exns))

theorem partitionExecutionOutcome.fst_spec {κ σ : Type} (outcomes : List (κ × ExecutionOutcome Int σ)) :
  ∀ (label : κ) (st : σ),
    (label, st) ∈ (partitionExecutionOutcome outcomes).fst ↔
    (label, ExecutionOutcome.success st) ∈ outcomes := by
  introv ; unfold partitionExecutionOutcome
  induction outcomes with
  | nil => simp
  | cons x l ih => rcases x with ⟨l, _ | _ | _⟩ <;> grind

-- NOTE: If this function is put inside `BaseSearchContext.checkViolationsAndMaybeTerminate`,
-- `specialize` of `List.filterMap` may not exhibit
def checkViolationsAndMaybeTerminate
  (completedDepth : Nat)
  (hasSuccessfulTransition : Bool)
  (assertionFailures : List (Int × σ)) :
  List (σₕ × ViolationKind) × Option (EarlyTerminationReason σₕ) :=
  -- Compute all violation conditions once
  let safetyViolations := params.invariants.filterMap fun p =>
    if !p.holdsOn th curr then some p.name else none
  let safetyViolation := !safetyViolations.isEmpty
  let deadlock := !hasSuccessfulTransition && !params.terminating.holdsOn th curr

  -- Collect all violations to add in a single list
  let newViolations : List (σₕ × ViolationKind) :=
    (if safetyViolation then [(fpSt, .safetyFailure safetyViolations)] else []) ++
    (if deadlock then [(fpSt, .deadlock)] else []) ++
    -- NOTE: This should be further optimized to avoid extra memory allocation
    (assertionFailures.map fun (exId, _) => (fpSt, .assertionFailure exId))

  let earlyTermination := params.earlyTerminationConditions.findSome? fun
    | .foundViolatingState => if safetyViolation then some (.foundViolatingState fpSt safetyViolations) else none
    | .reachedDepthBound bound => if completedDepth >= bound then some (.reachedDepthBound bound) else none
    | .deadlockOccurred => if deadlock then some (.deadlockOccurred fpSt) else none
    | .assertionFailed => assertionFailures.head?.map fun (exId, _) => .assertionFailed fpSt exId
    | .cancelled => none  -- Cancellation is handled externally via cancel token, not through early termination conditions
  (newViolations, earlyTermination)

/-- Process the current state, queuing its successors. -/
-- @[inline, specialize]
def BaseSearchContext.processState
  (outcomes : List (κ × ExecutionOutcome ℤ σ))
  (ctx : BaseSearchContext σ κ σₕ) : BaseSearchContext σ κ σₕ × Option (List (κ × σ)) :=
  let (successfulTransitions, assertionFailures) := partitionExecutionOutcome outcomes
  let hasSuccessfulTransition := !successfulTransitions.isEmpty
  let completedDepth := ctx.completedDepth
  let (newViolations, earlyTermination) :=
    checkViolationsAndMaybeTerminate params th fpSt curr completedDepth hasSuccessfulTransition assertionFailures
  let ctx := {ctx with violatingStates := newViolations ++ ctx.violatingStates}
  -- Check for violations, record them, and determine if we should terminate early
  let ctx := match earlyTermination with
    | some x =>
      match x with
      | .foundViolatingState fp violations => {ctx with finished := some (.earlyTermination (.foundViolatingState fp violations))}
      | .reachedDepthBound bound => {ctx with finished := some (.earlyTermination (.reachedDepthBound bound))}
      | .deadlockOccurred fp => {ctx with finished := some (.earlyTermination (.deadlockOccurred fp))}
      | .assertionFailed fp exId => {ctx with finished := some (.earlyTermination (.assertionFailed fp exId))}
      | .cancelled => {ctx with finished := some (.earlyTermination .cancelled)}
    | none => ctx
  (ctx, if earlyTermination.isSome then none else some successfulTransitions)

end Veil.ModelChecker.Concrete
