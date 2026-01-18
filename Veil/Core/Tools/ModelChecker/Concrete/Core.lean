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
structure BaseSearchContext {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
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
  (params : SearchParameters ρ σ)
  (inQueue : QueueItem σₕ σ → Prop)
  (seen : σₕ → Prop) : Prop
where
  queue_sound        : ∀ x : σ, ∀ d : Nat, inQueue ⟨fp.view x, x, d⟩ → sys.reachable x
  visited_sound      : Function.Injective fp.view → ∀ x, seen (fp.view x) → sys.reachable x
  queue_sub_visited  : ∀ x : σ, ∀ d : Nat, inQueue ⟨fp.view x, x, d⟩ → seen (fp.view x)
  queue_wellformed   : ∀ fingerprint st d, inQueue ⟨fingerprint, st, d⟩ → fingerprint = fp.view st


@[inline, specialize]
def BaseSearchContext.hasFinished {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params) : Bool := ctx.finished.isSome

@[inline]
def BaseSearchContext.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ) :
  @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params :=
  let initStates := sys.initStates |> Functor.map fp.view
  {
    seen := HashSet.insertMany HashSet.emptyWithCapacity initStates,
    log := Std.HashMap.emptyWithCapacity,
    violatingStates := [],
    finished := none,
    completedDepth := 0,
    currentFrontierDepth := 0,
    statesFound := initStates.length,
    actionStatsMap := {}
  }

def SearchContextInvariants.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ) :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (· ∈ (sys.initStates |> Functor.map (fun s => ⟨fp.view s, s, 0⟩)))
    (· ∈ (sys.initStates |> Functor.map fp.view)) := {
    queue_sound := by dsimp only [Functor.map]; grind
    visited_sound := by
      dsimp only [Functor.map]
      intro h_view_inj x h_in
      simp only [List.mem_map] at h_in
      obtain ⟨s, h_s_in, h_eq_view⟩ := h_in
      have h_eq_st : s = x := h_view_inj h_eq_view
      rw [← h_eq_st]
      exact EnumerableTransitionSystem.reachable.init s h_s_in
    queue_sub_visited := by dsimp only [Functor.map]; grind
    queue_wellformed := by dsimp only [Functor.map]; grind
  }



/-- Check a state for violations and optionally terminate early.
Returns the updated context with any violations recorded, and optionally
an early termination condition if we should stop the search.
This function ONLY modifies the `violatingStates` field, keeping all other fields unchanged. -/
@[inline, specialize]
def BaseSearchContext.checkViolationsAndMaybeTerminate {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq κ] [Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (fpSt : σₕ)
  (currSt : σ)
  (outcomes : List (κ × ExecutionOutcome Int σ))
  : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params × Option (EarlyTerminationReason σₕ) :=
  match ctx.finished with
  | some (.earlyTermination condition) => (ctx, some condition)
  | _ =>
    -- Compute all violation conditions once
    let safetyViolations := params.invariants.filterMap fun p =>
      if !p.holdsOn th currSt then some p.name else none
    let safetyViolation := !safetyViolations.isEmpty
    let hasSuccessfulTransition := outcomes.any fun (_, outcome) =>
      match outcome with | .success _ => true | _ => false
    let deadlock := !hasSuccessfulTransition && !params.terminating.holdsOn th currSt
    let assertionFailures := outcomes.filterMap fun (_, outcome) =>
      match outcome with | .assertionFailure exId _ => some exId | _ => none

    -- Collect all violations to add in a single list
    let newViolations : List (σₕ × ViolationKind) :=
      (if safetyViolation then [(fpSt, .safetyFailure safetyViolations)] else []) ++
      (if deadlock then [(fpSt, .deadlock)] else []) ++
      (assertionFailures.map fun exId => (fpSt, .assertionFailure exId))

    -- Update context with all violations at once (only modifying violatingStates)
    let ctx := {ctx with violatingStates := newViolations ++ ctx.violatingStates}
    let earlyTermination := params.earlyTerminationConditions.findSome? fun
      | .foundViolatingState => if safetyViolation then some (.foundViolatingState fpSt safetyViolations) else none
      | .reachedDepthBound bound => if ctx.completedDepth >= bound then some (.reachedDepthBound bound) else none
      | .deadlockOccurred => if deadlock then some (.deadlockOccurred fpSt) else none
      | .assertionFailed => assertionFailures.head?.map (.assertionFailed fpSt)
      | .cancelled => none  -- Cancellation is handled externally via cancel token, not through early termination conditions
    (ctx, earlyTermination)


/-- Process the current state, queuing its successors. -/
@[inline, specialize]
def BaseSearchContext.processState {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)
  -- (depth : Nat)  -- depth of the current state
  (curr : σ)
  -- (h_curr : sys.reachable curr)
  (ctx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params) :
  (@BaseSearchContext ρ σ κ σₕ fp _ _ th sys params ×
    Option ({ l : List (κ × ExecutionOutcome Int σ) // l = sys.tr th curr })) :=
  let outcomes := sys.tr th curr
  -- Check for violations, record them, and determine if we should terminate early
  match ctx.checkViolationsAndMaybeTerminate sys fpSt curr outcomes with
  | (ctx, some (.foundViolatingState fp violations)) => ({ctx with finished := some (.earlyTermination (.foundViolatingState fp violations))}, none)
  | (ctx, some (.reachedDepthBound bound)) => ({ctx with finished := some (.earlyTermination (.reachedDepthBound bound))}, none)
  | (ctx, some (.deadlockOccurred fp)) => ({ctx with finished := some (.earlyTermination (.deadlockOccurred fp))}, none)
  | (ctx, some (.assertionFailed fp exId)) => ({ctx with finished := some (.earlyTermination (.assertionFailed fp exId))}, none)
  | (ctx, some .cancelled) => ({ctx with finished := some (.earlyTermination .cancelled)}, none)
  -- If not terminating early, explore all neighbors of the current state
  | (ctx, none) => (ctx, some ⟨outcomes, rfl⟩)


theorem BaseSearchContext.processState_returns_some_implies_not_finished {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Hashable κ] [Repr σ] [Repr σₕ]
  {th : ρ} {params : _}
  (sys : _)
  (fpSt : σₕ)
  (curr : σ)
  (ctx : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (ctx' : @BaseSearchContext ρ σ κ σₕ fp _ _ th sys params)
  (outcomes : { l : List (κ × ExecutionOutcome Int σ) // l = sys.tr th curr })
  (h_input_not_finished : ¬ ctx.finished = some .exploredAllReachableStates)
  (h_process : ctx.processState sys fpSt curr = (ctx', some outcomes)) :
  ctx'.finished.isSome = false := by
  unfold processState at h_process
  simp only at h_process
  split at h_process <;> try (injection h_process with _ h_snd; simp at h_snd)
  rename_i ctx_temp heq_check h_split
  rw [← h_split]
  unfold checkViolationsAndMaybeTerminate at heq_check
  simp only at heq_check
  split at heq_check
  · injection heq_check with _ h_opt_eq
    simp at h_opt_eq
  · injection heq_check with h_ctx_temp_eq h_opt_eq
    rw [← h_ctx_temp_eq]
    simp only
    cases h_finished : ctx.finished
    · simp
    · rename_i reason
      cases reason
      · contradiction
      · simp [h_finished] at *



/-- Theorem: checkViolationsAndMaybeTerminate preserves key fields of BaseSearchContext.
    This is critical for proving that processState doesn't unexpectedly modify the search context. -/
theorem BaseSearchContext.checkViolationsAndMaybeTerminate_preserves_fields {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @BaseSearchContext ρ σ κ σₕ fp instBEq instHash th sys params)
  (fpSt : σₕ)
  (currSt : σ)
  (outcomes : List (κ × ExecutionOutcome Int σ)) :
  let ⟨post, _⟩ := ctx.checkViolationsAndMaybeTerminate sys fpSt currSt outcomes
  post.seen = ctx.seen ∧
  post.log = ctx.log ∧
  post.finished = ctx.finished ∧
  post.completedDepth = ctx.completedDepth ∧
  post.currentFrontierDepth = ctx.currentFrontierDepth ∧
  post.statesFound = ctx.statesFound ∧
  post.actionStatsMap = ctx.actionStatsMap := by
  simp only [checkViolationsAndMaybeTerminate]
  split<;> simp


/-- Theorem: processState preserves the seen field.
    This is essential for maintaining invariants during state exploration. -/
theorem BaseSearchContext.processState_preserves_seen {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  [BEq σ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (fpSt : σₕ)
  (curr : σ)
  (ctx : @BaseSearchContext ρ σ κ σₕ fp instBEq instHash th sys params) :
  (ctx.processState sys fpSt curr).1.seen = ctx.seen := by
  unfold BaseSearchContext.processState
  simp only
  have h := checkViolationsAndMaybeTerminate_preserves_fields sys params ctx fpSt curr (sys.tr th curr)
  split <;>
  grind



/-- Extract successful transitions from a list of outcomes. -/
@[inline]
def extractSuccessfulTransitions (outcomes : List (κ × ExecutionOutcome Int σ)) : List (κ × σ) :=
  outcomes.filterMap fun (label, outcome) =>
    match outcome with
    | .success st => some (label, st)
    | _ => none

end Veil.ModelChecker.Concrete
