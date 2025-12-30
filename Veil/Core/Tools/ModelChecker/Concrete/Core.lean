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

@[inline, specialize]
def BaseSearchContext.hasFinished {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)) th)
  (params : SearchParameters ρ σ)
  (ctx : @BaseSearchContext ρ σ κ σₕ fp th sys params) : Bool := ctx.finished.isSome

@[inline]
def BaseSearchContext.initial {ρ σ κ σₕ : Type}
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

end Veil.ModelChecker.Concrete
