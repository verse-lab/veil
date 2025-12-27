import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.ModelChecker.Interface
import Veil.Core.Tools.ModelChecker.Concrete.FunctionalQueue
import Veil.Core.Tools.ModelChecker.Trace

namespace Veil.ModelChecker.Concrete
open Std

/-- A function that maps a full state to a view of the state. -/
class StateView (FullState View : Type) where
  view : FullState → View

class abbrev StateFingerprint (FullState View : Type) := BEq View, LawfulBEq View, Hashable View, LawfulHashable View, StateView FullState View

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

/-- A model checker search context is parametrised by the system that's being
checked and the theory it's being checked under. -/
structure BaseSearchContext {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
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

structure SearchContextInvariants {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ)
  (inQueue : QueueItem σₕ σ → Prop)
  (seen : σₕ → Prop) : Prop
where
  queue_sound        : ∀ x : σ, ∀ d : Nat, inQueue ⟨fp.view x, x, d⟩ → sys.reachable x
  visited_sound      : Function.Injective fp.view → ∀ x, seen (fp.view x) → sys.reachable x
  queue_sub_visited  : ∀ x : σ, ∀ d : Nat, inQueue ⟨fp.view x, x, d⟩ → seen (fp.view x)
  queue_wellformed   : ∀ fingerprint st d, inQueue ⟨fingerprint, st, d⟩ → fingerprint = fp.view st
  /-
  Can these be merged into two invariants?
  queue_invariant : ∀ h x d, (h, x, d) ∈ queue → h = fp.view x ∧ sys.reachable x ∧ h ∈ seen
  visited_sound : (same)

  Also, might weaken `visited_sound` into `∀ h, seen h → ∃ x, fp.view x = h ∧ sys.reachable x`,
  according to the following theorem:

  theorem visited_sound_imp
    [fp : StateFingerprint σ σₕ]
    (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
    (seen : σₕ → Bool) :
    (∀ h, seen h → ∃ x, fp.view x = h ∧ sys.reachable x) →
    (Function.Injective fp.view → ∀ x, seen (fp.view x) → sys.reachable x) := by
    intro h hinj x hseen
    specialize h _ hseen
    rcases h with ⟨x', heq, hr⟩ ; have tmp := hinj heq ; subst x' ; assumption
  -/

structure SequentialSearchContext {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ)
extends @BaseSearchContext ρ σ κ σₕ fp th sys params
where
  /-- Queue storing (fingerprint, state, depth) tuples for BFS traversal -/
  sq    : fQueue (QueueItem σₕ σ)
  invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (Membership.mem sq) (Membership.mem seen)

structure ParallelSearchContextMain {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ)
extends @BaseSearchContext ρ σ κ σₕ fp th sys params
where
  /-- Recording the nodes to visit in the next depth. Due to the way
  parallel BFS works, it could be any data structure that supports `O(1)`
  element insertion (e.g., `Array`); but to support efficient merging,
  it's made to be an `HashMap`. -/
  tovisit : Std.HashMap σₕ (σ × Nat)
  invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (fun ⟨h, x, d⟩ => tovisit[h]? = some (x, d)) (Membership.mem seen)

structure ParallelSearchContextSub {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ)
extends @BaseSearchContext ρ σ κ σₕ fp th sys params
where
  tovisit : Array (QueueItem σₕ σ)
  localSeen : Std.HashSet σₕ
  localLog : Std.HashMap σₕ (σₕ × κ)
  invs  : @SearchContextInvariants ρ σ κ σₕ fp th sys params (Membership.mem tovisit) (fun h => h ∈ seen ∨ h ∈ localSeen)

def ParallelSearchContextSub.merge1 {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] {th : ρ} {sys : _} {params : _}
  (mainCtx : @ParallelSearchContextMain ρ σ κ σₕ fp th sys params)
  (subCtx : @ParallelSearchContextSub ρ σ κ σₕ fp th sys params) :
  @ParallelSearchContextMain ρ σ κ σₕ fp th sys params := {
    mainCtx with
      seen := mainCtx.seen.union subCtx.localSeen,
      log := mainCtx.log.union subCtx.localLog,
      violatingStates := subCtx.violatingStates ++ mainCtx.violatingStates,
      finished := Option.or mainCtx.finished subCtx.finished
      -- do not update depth information here
      tovisit := subCtx.tovisit.foldl (init := mainCtx.tovisit) fun acc ⟨h, x, d⟩ => acc.insertIfNew h (x, d)
      invs := sorry
  }

def ParallelSearchContextSub.merge2 {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ] {th : ρ} {sys : _} {params : _}
  (mainCtx : @ParallelSearchContextMain ρ σ κ σₕ fp th sys params)
  (subCtx : @ParallelSearchContextSub ρ σ κ σₕ fp th sys params) :
  @ParallelSearchContextMain ρ σ κ σₕ fp th sys params := {
    mainCtx with
      tovisit := subCtx.tovisit.foldl (init := mainCtx.tovisit) fun acc ⟨h, x, d⟩ =>
        if !mainCtx.seen.contains h then acc.insertIfNew h (x, d) else acc
      invs := sorry
  }

@[inline, specialize]
def BaseSearchContext.hasFinished {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @BaseSearchContext ρ σ κ σₕ fp th sys params) : Bool := ctx.finished.isSome

@[inline]
def BaseSequentialSearchContext.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ) :
  @BaseSearchContext ρ σ κ σₕ fp th sys params := {
    seen := HashSet.insertMany HashSet.emptyWithCapacity (sys.initStates |> Functor.map fp.view),
    log := Std.HashMap.emptyWithCapacity,
    violatingStates := [],
    finished := none,
    completedDepth := 0,
    currentFrontierDepth := 0
  }

def SearchContextInvariants.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ) :
  @SearchContextInvariants ρ σ κ σₕ fp th sys params
    (· ∈ (sys.initStates |> Functor.map (fun s => ⟨fp.view s, s, 0⟩)))
    (· ∈ (sys.initStates |> Functor.map fp.view)) := {
    /-
    queue_sound := by dsimp only [Functor.map]; intros; grind
    visited_sound := by
      dsimp only [Functor.map]
      intro h_view_inj x h_in
      have h_in_init : x ∈ sys.initStates := by {
        have h_in_list : fp.view x ∈ (sys.initStates).map fp.view := by
          { grind [Std.HashSet.mem_of_mem_insertMany_list] }
        rw [List.mem_map] at h_in_list
        obtain ⟨s, h_s_in, h_eq_view⟩ := h_in_list
        have h_eq_st : s = x := h_view_inj h_eq_view
        grind
      }
      grind
    queue_sub_visited := by dsimp only [Functor.map]; intros; grind
    queue_wellformed := by dsimp only [Functor.map]; intros; grind
    -/
    queue_sound := by sorry
    visited_sound := by sorry
    queue_sub_visited := by sorry
    queue_wellformed := by sorry
  }

def SequentialSearchContext.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ) :
  @SequentialSearchContext ρ σ κ σₕ fp th sys params := {
    BaseSequentialSearchContext.initial sys params with
    sq := fQueue.ofList (sys.initStates |> Functor.map (fun s => ⟨fp.view s, s, 0⟩)),
    invs := sorry
  }

def ParallelSearchContextMain.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ) :
  @ParallelSearchContextMain ρ σ κ σₕ fp th sys params := {
    BaseSequentialSearchContext.initial sys params with
    tovisit := Std.HashMap.ofList (sys.initStates |> Functor.map (fun s => ⟨fp.view s, s, 0⟩))
    invs := sorry
  }

/-- Process a single neighbor node during BFS traversal.
If the neighbor has been seen, return the current context unchanged.
Otherwise, add it to seen set and log, then enqueue it. -/
@[inline, specialize]
def SequentialSearchContext.tryExploreNeighbor {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)  -- fingerprint of state we're coming from (pre-state), for logging
  (depth : Nat)  -- depth of the current state (neighbor will be at depth + 1)
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp th sys params)
  (neighbor : κ × σ)
  (h_neighbor : sys.reachable neighbor.2) :
  @SequentialSearchContext ρ σ κ σₕ fp th sys params :=
  let ⟨label, succ⟩ := neighbor
  let fingerprint := fp.view succ
  if ctx.seen.contains fingerprint then ctx
  else
    let ctx_with_seen : @SequentialSearchContext ρ σ κ σₕ fp th sys params := {
      ctx with
        seen := ctx.seen.insert fingerprint,
        log := ctx.log.insert fingerprint (fpSt, label),
        invs := by
          constructor
          · -- queue_sound: queue unchanged, so invariant preserved
            intro x d h_in_queue
            exact ctx.invs.queue_sound x d h_in_queue
          · -- visited_sound: new seen element is the reachable neighbor
            intro h_view_inj x h_in_seen
            rw [Membership.mem] at h_in_seen
            by_cases h : fp.view x = fingerprint
            · have : x = succ := h_view_inj h
              rw [this]; exact h_neighbor
            · have h_in_old : ctx.seen.contains (fp.view x) := by grind
              exact ctx.invs.visited_sound h_view_inj x h_in_old
          · -- queue_sub_visited: queue unchanged, but seen expanded
            intro x d h_in_queue
            have h_old := ctx.invs.queue_sub_visited x d h_in_queue
            rw [Membership.mem]
            grind
          · -- queue_wellformed: queue unchanged
            intro fp' st d h_in_queue
            exact ctx.invs.queue_wellformed fp' st d h_in_queue
    }
    { ctx_with_seen with
        sq := ctx_with_seen.sq.enqueue ⟨fingerprint, succ, depth + 1⟩,
        invs := by
          constructor
          · -- queue_sound: new element in queue is reachable
            intro x d h_in_queue
            simp only [Membership.mem, fQueue.enqueue] at h_in_queue
            rcases h_in_queue with h_in_front | h_in_back
            · -- x was already in the old queue (front unchanged)
              exact ctx_with_seen.invs.queue_sound x d (Or.inl h_in_front)
            · -- x is in the back, which now includes the new element
              have : ⟨fp.view x, x, d⟩ ∈ (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ) :: ctx_with_seen.sq.back := h_in_back
              simp only [List.mem_cons] at this
              rcases this with h_eq | h_in_old_back
              · -- x is the newly enqueued element: ⟨fp.view x, x, d⟩ = ⟨fingerprint, succ, depth + 1⟩
                have h_x : x = succ := by
                  have := congrArg QueueItem.state h_eq
                  exact this
                rw [h_x]
                exact h_neighbor
              · -- x was in the old back
                exact ctx_with_seen.invs.queue_sound x d (Or.inr h_in_old_back)
          · -- visited_sound: seen unchanged
            intro h_view_inj x h_in_seen
            exact ctx_with_seen.invs.visited_sound h_view_inj x h_in_seen
          · -- queue_sub_visited: new queue element's fingerprint is in seen
            intro x d h_in_queue
            simp only [Membership.mem, fQueue.enqueue] at h_in_queue
            rcases h_in_queue with h_in_front | h_in_back
            · exact ctx_with_seen.invs.queue_sub_visited x d (Or.inl h_in_front)
            · have : ⟨fp.view x, x, d⟩ ∈ (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ) :: ctx_with_seen.sq.back := h_in_back
              simp only [List.mem_cons] at this
              rcases this with h_eq | h_in_old_back
              · -- The new element: its fingerprint was just added to seen
                have h_fp : fp.view x = fingerprint := by
                  have := congrArg QueueItem.fingerprint h_eq
                  exact this
                rw [h_fp, Membership.mem]
                grind
              · exact ctx_with_seen.invs.queue_sub_visited x d (Or.inr h_in_old_back)
          · -- queue_wellformed: new element has matching fingerprint
            intro fp' st d h_in_queue
            simp only [Membership.mem, fQueue.enqueue] at h_in_queue
            rcases h_in_queue with h_in_front | h_in_back
            · exact ctx_with_seen.invs.queue_wellformed fp' st d (Or.inl h_in_front)
            · have : ⟨fp', st, d⟩ ∈ (⟨fingerprint, succ, depth + 1⟩ : QueueItem σₕ σ) :: ctx_with_seen.sq.back := h_in_back
              simp only [List.mem_cons] at this
              rcases this with h_eq | h_in_old_back
              · -- The new element: fp' = fingerprint and st = succ
                have h_fp' : fp' = fingerprint := by
                  have := congrArg QueueItem.fingerprint h_eq
                  exact this
                have h_st : st = succ := by
                  have := congrArg QueueItem.state h_eq
                  exact this
                rw [h_st, h_fp']
              · exact ctx_with_seen.invs.queue_wellformed fp' st d (Or.inr h_in_old_back)
    }

@[inline, specialize]
def ParallelSearchContextSub.tryExploreNeighbor {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)  -- fingerprint of state we're coming from (pre-state), for logging
  (depth : Nat)  -- depth of the current state (neighbor will be at depth + 1)
  (ctx : @ParallelSearchContextSub ρ σ κ σₕ fp th sys params)
  (neighbor : κ × σ)
  (h_neighbor : sys.reachable neighbor.2) :
  @ParallelSearchContextSub ρ σ κ σₕ fp th sys params :=
  let ⟨label, succ⟩ := neighbor
  let fingerprint := fp.view succ
  if ctx.seen.contains fingerprint || ctx.localSeen.contains fingerprint then ctx
  else
    let ctx_with_seen : @ParallelSearchContextSub ρ σ κ σₕ fp th sys params := {
      ctx with
        localSeen := ctx.localSeen.insert fingerprint,
        localLog := ctx.localLog.insert fingerprint (fpSt, label),
        invs := sorry
    }
    { ctx_with_seen with
        tovisit := ctx_with_seen.tovisit.push ⟨fingerprint, succ, depth + 1⟩,
        invs := sorry
    }

/-- Check a state for violations and optionally terminate early.
Returns the updated context with any violations recorded, and optionally
an early termination condition if we should stop the search. -/
@[inline, specialize]
def BaseSearchContext.checkViolationsAndMaybeTerminate {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @BaseSearchContext ρ σ κ σₕ fp th sys params)
  (fpSt : σₕ)
  (currSt : σ)
  (successors : List (κ × σ))
  : @BaseSearchContext ρ σ κ σₕ fp th sys params × Option (EarlyTerminationReason σₕ) :=
  -- Check for previously recorded termination
  match ctx.finished with
  | some (.earlyTermination condition) => (ctx, some condition)
  | _ =>
    -- Check for violations (compute once, use for both recording and early termination)
    let safetyViolations := params.invariants.filterMap (fun p => if !p.holdsOn th currSt then some p.name else none)
    let safetyViolation := !safetyViolations.isEmpty
    let deadlock := successors.isEmpty && !params.terminating.holdsOn th currSt
    -- Record violations in context
    let ctx := if safetyViolation then {ctx with violatingStates := (fpSt, .safetyFailure safetyViolations) :: ctx.violatingStates} else ctx
    let ctx := if deadlock then {ctx with violatingStates := (fpSt, .deadlock) :: ctx.violatingStates} else ctx
    -- Check for early termination using the same computed values
    let earlyTermination := params.earlyTerminationConditions.findSome? (fun sc => match sc with
      | EarlyTerminationCondition.foundViolatingState =>
          if safetyViolation then some (.foundViolatingState fpSt safetyViolations) else none
      | EarlyTerminationCondition.reachedDepthBound bound =>
          if ctx.completedDepth >= bound then some (.reachedDepthBound bound) else none
      | EarlyTerminationCondition.deadlockOccurred =>
          if deadlock then some (.deadlockOccurred fpSt) else none
    )
    (ctx, earlyTermination)

/-- Process the current state, queuing its successors. -/
@[inline, specialize]
def BaseSearchContext.processState {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)
  -- (depth : Nat)  -- depth of the current state
  (curr : σ)
  -- (h_curr : sys.reachable curr)
  (ctx : @BaseSearchContext ρ σ κ σₕ fp th sys params) :
  (@BaseSearchContext ρ σ κ σₕ fp th sys params ×
    Option ({ l : List (κ × σ) // l = sys.tr th curr })) :=
  let successors := sys.tr th curr
  -- Check for violations, record them, and determine if we should terminate early
  match ctx.checkViolationsAndMaybeTerminate sys fpSt curr successors with
  | (ctx, some (.foundViolatingState fp violations)) => ({ctx with finished := some (.earlyTermination (.foundViolatingState fp violations))}, none)
  | (ctx, some (.reachedDepthBound bound)) => ({ctx with finished := some (.earlyTermination (.reachedDepthBound bound))}, none)
  | (ctx, some (.deadlockOccurred fp)) => ({ctx with finished := some (.earlyTermination (.deadlockOccurred fp))}, none)
  -- If not terminating early, explore all neighbors of the current state
  | (ctx, none) => (ctx, some ⟨successors, rfl⟩)

@[inline, specialize]
def SequentialSearchContext.processState {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)
  (depth : Nat)  -- depth of the current state
  (curr : σ)
  (h_curr : sys.reachable curr)
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp th sys params) :
  @SequentialSearchContext ρ σ κ σₕ fp th sys params :=
  let (baseCtx', successorsOpt) := ctx.toBaseSearchContext.processState sys fpSt curr
  match successorsOpt with
  | none => { ctx with
      toBaseSearchContext := baseCtx'
      invs := sorry
    }
  | some ⟨successors, heq⟩ =>
      let ctx_updated := { ctx with toBaseSearchContext := baseCtx', invs := sorry }
      successors.attach.foldl (fun current_ctx ⟨⟨tr, postState⟩, h_neighbor_in_tr⟩ =>
      if current_ctx.hasFinished then current_ctx
      else
        let h_neighbor_reachable : sys.reachable postState :=
          EnumerableTransitionSystem.reachable.step curr postState h_curr ⟨tr, heq ▸ h_neighbor_in_tr⟩
        SequentialSearchContext.tryExploreNeighbor sys fpSt depth current_ctx ⟨tr, postState⟩ h_neighbor_reachable
    ) ctx_updated

@[inline, specialize]
def ParallelSearchContextSub.processState {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)
  (depth : Nat)  -- depth of the current state
  (curr : σ)
  (h_curr : sys.reachable curr)
  (ctx : @ParallelSearchContextSub ρ σ κ σₕ fp th sys params) :
  @ParallelSearchContextSub ρ σ κ σₕ fp th sys params :=
  let (baseCtx', successorsOpt) := ctx.toBaseSearchContext.processState sys fpSt curr
  match successorsOpt with
  | none => { ctx with
      toBaseSearchContext := baseCtx'
      invs := sorry
    }
  | some ⟨successors, heq⟩ =>
      let ctx_updated := { ctx with toBaseSearchContext := baseCtx', invs := sorry }
      successors.attach.foldl (fun current_ctx ⟨⟨tr, postState⟩, h_neighbor_in_tr⟩ =>
      if current_ctx.hasFinished then current_ctx
      else
        let h_neighbor_reachable : sys.reachable postState :=
          EnumerableTransitionSystem.reachable.step curr postState h_curr ⟨tr, heq ▸ h_neighbor_in_tr⟩
        ParallelSearchContextSub.tryExploreNeighbor sys fpSt depth current_ctx ⟨tr, postState⟩ h_neighbor_reachable
    ) ctx_updated

/-- Perform one step of BFS. -/
@[inline, specialize]
def SequentialSearchContext.bfsStep {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @SequentialSearchContext ρ σ κ σₕ fp th sys params) :
  @SequentialSearchContext ρ σ κ σₕ fp th sys params :=
  match ctx.sq.dequeue? with
  | none => { ctx with finished := some (.exploredAllReachableStates) }
  | some (⟨fpSt, curr, depth⟩, q_tail) =>
    have h_curr : sys.reachable curr := sorry
    -- Update completed depth when we move to a new frontier level
    let (newCompletedDepth, newFrontierDepth) :=
      if depth > ctx.currentFrontierDepth then
        (depth - 1, depth)  -- All states at previous depth are now fully explored
      else
        (ctx.completedDepth, ctx.currentFrontierDepth)
    let ctx_dequeued : @SequentialSearchContext ρ σ κ σₕ fp th sys params := {
      ctx with
        sq := q_tail,
        completedDepth := newCompletedDepth,
        currentFrontierDepth := newFrontierDepth,
        invs := sorry
    }
    SequentialSearchContext.processState sys fpSt depth curr h_curr ctx_dequeued

@[inline, specialize]
def ParallelSearchContextSub.bfsBigStep {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (baseCtx : @BaseSearchContext ρ σ κ σₕ fp th sys params)
  (queue : Array (σₕ × σ × Nat)) :
  @ParallelSearchContextSub ρ σ κ σₕ fp th sys params :=
  let ctx : @ParallelSearchContextSub ρ σ κ σₕ fp th sys params := {
    baseCtx with
    tovisit := #[],
    localSeen := HashSet.emptyWithCapacity,
    localLog := Std.HashMap.emptyWithCapacity,
    invs := sorry
  }
  queue.foldl (init := ctx) fun current_ctx ⟨fpSt, curr, depth⟩ =>
    have h_curr : sys.reachable curr := sorry
    ParallelSearchContextSub.processState sys fpSt depth curr h_curr current_ctx

@[specialize]
def breadthFirstSearchSequential {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ) :
  @SequentialSearchContext ρ σ κ σₕ fp th sys params := Id.run do
  let mut ctx : @SequentialSearchContext ρ σ κ σₕ fp th sys params := SequentialSearchContext.initial sys params
  while !ctx.hasFinished do
    ctx := SequentialSearchContext.bfsStep sys ctx
  return ctx

@[specialize]
def breadthFirstSearchParallel {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq σ] [BEq κ] [Repr σ] [Repr σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ)
  (parallelCfg : ParallelConfig) :
  @ParallelSearchContextMain ρ σ κ σₕ fp th sys params := Id.run do
  let mut ctx : @ParallelSearchContextMain ρ σ κ σₕ fp th sys params := ParallelSearchContextMain.initial sys params
  while !ctx.hasFinished do
    -- In this setting, the queue emptiness check needs to be done here
    if ctx.tovisit.isEmpty then
      ctx := { ctx with finished := some (.exploredAllReachableStates) }
      return ctx
    let tovisitArr := ctx.tovisit.toArray
    ctx := {ctx with
      tovisit := Std.HashMap.emptyWithCapacity,
      completedDepth := ctx.currentFrontierDepth,
      currentFrontierDepth := ctx.currentFrontierDepth + 1,
      invs := sorry
    }
    let tasks := parallelCfg.taskSplit (ParallelSearchContextSub.bfsBigStep sys ctx.toBaseSearchContext) tovisitArr
    let results := tasks.map Task.get
    -- compute `seen` first, and then merge the `tovisit`s, since need to
    -- filter out already seen states when merging
    ctx := results.foldl (init := ctx) ParallelSearchContextSub.merge1
    ctx := results.foldl (init := ctx) ParallelSearchContextSub.merge2
  return ctx

/-! ## Trace Recovery

These functions reconstruct a full trace with concrete states from a SearchContext
that contains fingerprint-based state references. -/

/-- Walk backward through the log to build a fingerprint-based path from a
state to an initial state. Returns `(initialStateFingerprint, steps)` where
each step has the transition label and the fingerprint of the post-state. -/
partial def retraceSteps [BEq σₕ] [Hashable σₕ]
  (log : Std.HashMap σₕ (σₕ × κ)) (cur : σₕ)
  (acc : List (Step σₕ κ) := []) : σₕ × List (Step σₕ κ) :=
  match log.get? cur with
  | none => (cur, acc)
  | some (prev, label) =>
    retraceSteps log prev ({ transitionLabel := label, nextState := cur } :: acc)

/-- Find a full state from a list that matches a given fingerprint. -/
@[inline, specialize]
def findByFingerprint [fp : StateFingerprint σ σₕ]
  (states : List σ) (targetFp : σₕ) (fallback : σ) : σ :=
  states.find? (fun s => fp.view s == targetFp) |>.getD fallback

/-- Reconstruct a full trace with concrete states from a SearchContext.
This re-executes transitions to recover full state objects from fingerprints.
The `targetFingerprint` parameter specifies which violating state's trace to recover. -/
def recoverTrace {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [Inhabited κ] [Inhabited σ] [Repr σₕ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  {params : SearchParameters ρ σ}
  (ctx : @BaseSearchContext ρ σ κ σₕ fp th sys params)
  (targetFingerprint : σₕ)
  : Trace ρ σ κ :=
  -- Retrace steps from the target fingerprint back to an initial state
  let (initFp, stepsFp) := retraceSteps ctx.log targetFingerprint
  -- Recover initial state by matching fingerprint
  let initialState := findByFingerprint sys.initStates initFp default
  -- Recover trace steps by re-executing transitions and matching fingerprints
  Id.run do
    let mut curSt := initialState
    let mut steps : Steps σ κ := #[]
    for step in stepsFp do
      let successors := sys.tr th curSt
      let (transitionLabel, nextSt) :=
        match successors.find? (fun (_, s) => fp.view s == step.nextState) with
        | some (tr, s) => (tr, s)
        | none => panic! s!"Could not recover transition from fingerprint {repr (fp.view curSt)} to {repr step.nextState}!"
      curSt := nextSt
      steps := steps.push { transitionLabel := transitionLabel, nextState := nextSt }
    return { theory := th, initialState := initialState, steps := steps }


/-! ## Model Checker -/

def findReachable {ρ σ κ : Type}
  [Inhabited κ] [Inhabited σ] [Repr σ]
  [BEq σ] [BEq κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  [fp : StateFingerprint σ UInt64]
  (params : SearchParameters ρ σ)
  (parallelCfg : Option ParallelConfig)
  : ModelCheckingResult ρ σ κ UInt64 :=
  let ctx :=
    match parallelCfg with
    | some cfg => breadthFirstSearchParallel sys params cfg |>.toBaseSearchContext
    | none     => breadthFirstSearchSequential sys params |>.toBaseSearchContext
  match ctx.finished with
  | some (.earlyTermination (.foundViolatingState fingerprint violations)) =>
    ModelCheckingResult.foundViolation fingerprint (.safetyFailure violations) (some (recoverTrace sys ctx fingerprint))
  | some (.earlyTermination (.deadlockOccurred fingerprint)) =>
    ModelCheckingResult.foundViolation fingerprint .deadlock (some (recoverTrace sys ctx fingerprint))
  | some (.earlyTermination (.reachedDepthBound _)) =>
    -- No violation found within depth bound; report number of states explored
    ModelCheckingResult.noViolationFound ctx.seen.size (.earlyTermination (.reachedDepthBound ctx.completedDepth))
  | some (.exploredAllReachableStates) =>
    if !ctx.violatingStates.isEmpty then
      let (fingerprint, violation) := ctx.violatingStates.head!
      ModelCheckingResult.foundViolation fingerprint violation (some (recoverTrace sys ctx fingerprint))
    else
      ModelCheckingResult.noViolationFound ctx.seen.size (.exploredAllReachableStates)
  | none => panic! s!"SearchContext.finished is none! This should never happen."

end Veil.ModelChecker.Concrete
