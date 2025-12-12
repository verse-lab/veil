import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.ModelChecker.Interface
import Veil.Core.Tools.ModelChecker.Concrete.FunctionalQueue

namespace Veil.ModelChecker.Concrete
open Std

/-- A function that maps a full state to a view of the state. -/
class StateView (FullState View : Type) where
  view : FullState → View

@[default_instance low] instance : StateView σ σ where
  view := id

class abbrev StateFingerprint (FullState View : Type) := BEq View, LawfulBEq View, Hashable View, LawfulHashable View, StateView FullState View

/-- A model checker search context is parametrised by the system that's being
checked and the theory it's being checked under. -/
structure SearchContext {ρ σ κ σₕ : Type} (SetT : Type → Type)
  [Collection SetT ρ] [Collection SetT σ] [Collection SetT (κ × σ)]
  [fp : StateFingerprint σ σₕ]
  (sys : EnumerableTransitionSystem ρ (SetT ρ) σ (SetT σ) κ (SetT (κ × σ)))
  (th : ρ) (hTh : th ∈ sys.theories)
  (params : SearchParameters ρ σ)
where
  seen  : Std.HashSet σₕ
  sq    : fQueue (σₕ × σ)
  /- We use a `HashMap σ_post (σ_pre × κ)` to store the log of transitions, which
  will make it easier to reconstruct counterexample trace. -/
  log                : Std.HashMap σₕ (σₕ × κ)
  violatingStates    : List σₕ
  /-- Have we finished the search? If so, why? -/
  finished           : Option StoppingCondition
  queue_sound        : ∀ x : σ, ⟨fp.view x, x⟩ ∈ fQueue.toList sq → sys.reachable th x
  visited_sound      : Function.Injective fp.view → ∀ x, (fp.view x) ∈ seen → sys.reachable th x
  queue_sub_visited  : ∀ x : σ, ⟨fp.view x, x⟩ ∈ fQueue.toList sq → (fp.view x) ∈ seen
  queue_wellformed   : ∀ fingerprint st, ⟨fingerprint, st⟩ ∈ fQueue.toList sq → fingerprint = fp.view st

@[inline, specialize]
def SearchContext.hasFinished {ρ σ κ σₕ : Type} {SetT : Type → Type}
  [Collection SetT ρ] [Collection SetT σ] [Collection SetT (κ × σ)]
  [fp : StateFingerprint σ σₕ]
  [sys : EnumerableTransitionSystem ρ (SetT ρ) σ (SetT σ) κ (SetT (κ × σ))]
  {th : ρ} {hTh : th ∈ sys.theories}
  (params : SearchParameters ρ σ)
  (ctx : @SearchContext ρ σ κ σₕ SetT _ _ _ fp sys th hTh params) : Bool := ctx.finished.isSome

def SearchContext.initial {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq ρ] [BEq σ] [BEq κ]
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ)))
  (th : ρ) (hTh : th ∈ sys.theories)
  (params : SearchParameters ρ σ) :
  @SearchContext ρ σ κ σₕ List _ _ _ fp sys th hTh params := {
    seen := HashSet.insertMany HashSet.emptyWithCapacity (sys.initStates th |> Functor.map fp.view),
    sq := fQueue.ofList (sys.initStates th |> Functor.map (fun s => (fp.view s, s))),
    log := Std.HashMap.emptyWithCapacity
    violatingStates := []
    finished := none
    queue_sound := by dsimp only [Functor.map]; intros; grind
    visited_sound := by
      dsimp only [Functor.map]
      intro h_view_inj x h_in
      have h_in_init : x ∈ (EnumerableTransitionSystem.initStates σ (List (κ × σ)) th) := by {
        have h_in_list : fp.view x ∈ ((EnumerableTransitionSystem.initStates σ (List (κ × σ)) th)).map fp.view := by
          { grind [Std.HashSet.mem_of_mem_insertMany_list] }
        rw [List.mem_map] at h_in_list
        obtain ⟨s, h_s_in, h_eq_view⟩ := h_in_list
        have h_eq_st : s = x := h_view_inj h_eq_view
        grind
      }
      grind
    queue_sub_visited := by dsimp only [Functor.map]; intros; grind
    queue_wellformed := by dsimp only [Functor.map]; intros; grind
  }

@[inline, specialize]
def SearchContext.shouldStop {ρ σ κ σₕ : Type} {SetT : Type → Type}
  [Collection SetT ρ] [Collection SetT σ] [Collection SetT (κ × σ)]
  [fp : StateFingerprint σ σₕ]
  [sys : EnumerableTransitionSystem ρ (SetT ρ) σ (SetT σ) κ (SetT (κ × σ))]
  {th : ρ} {hTh : th ∈ sys.theories}
  {params : SearchParameters ρ σ}
  (ctx : @SearchContext ρ σ κ σₕ SetT _ _ _ fp sys th hTh params)
  (currSt : σ)
  : Option StoppingCondition :=
  ctx.finished.orElse (fun () =>
    params.stoppingConditions.findSome? (fun sc => match sc with
    | StoppingCondition.exploredAllReachableStates => if ctx.sq.dequeue?.isNone then some sc else none
    | StoppingCondition.foundViolatingState => if !params.safety.holdsOn th currSt then some sc else none
  ))


/-- Process a single neighbor node during BFS traversal.
If the neighbor has been seen, return the current context unchanged.
Otherwise, add it to seen set and log, then enqueue it. -/
@[inline, specialize]
def SearchContext.tryExploreNeighbor {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq ρ] [BEq σ] [BEq κ]
  [sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ))]
  {th : ρ} {hTh : th ∈ sys.theories}
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)  -- fingerprint of state we're coming from (pre-state), for logging
  (ctx : @SearchContext ρ σ κ σₕ List _ _ _ fp sys th hTh params)
  (neighbor : κ × σ)
  (h_neighbor : sys.reachable th neighbor.2) :
  @SearchContext ρ σ κ σₕ List _ _ _ fp sys th hTh params :=
  let ⟨label, succ⟩ := neighbor
  let fingerprint := fp.view succ
  if ctx.seen.contains fingerprint then ctx
  else
    let ctx_with_seen : @SearchContext ρ σ κ σₕ List _ _ _ fp sys th hTh params := {
      ctx with
        seen := ctx.seen.insert fingerprint,
        log := ctx.log.insert fingerprint (fpSt, label),
        queue_sound := sorry
        visited_sound := sorry
        queue_sub_visited := sorry
        queue_wellformed := ctx.queue_wellformed
    }
    { ctx_with_seen with
        sq := ctx_with_seen.sq.enqueue (fingerprint, succ),
        queue_sound := sorry
        queue_sub_visited := sorry
        queue_wellformed := sorry
    }

/-- Process the current state, queuing its successors. -/
@[inline, specialize]
def SearchContext.processState {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq ρ] [BEq σ] [BEq κ]
  [sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ))]
  {th : ρ} {hTh : th ∈ sys.theories}
  {params : SearchParameters ρ σ}
  (fpSt : σₕ)
  (curr : σ)
  (h_curr : sys.reachable th curr)
  (ctx : @SearchContext ρ σ κ σₕ List _ _ _ fp sys th hTh params) :
  @SearchContext ρ σ κ σₕ List _ _ _ fp sys th hTh params :=
  -- Check whether we should stop the search
  match ctx.shouldStop curr with
  | some sc => { ctx with finished := some sc }
  -- If not, explore all neighbors of the current state
  | none => (sys.tr th curr).attach.foldl (fun current_ctx ⟨⟨tr, postState⟩, h_neighbor_in_tr⟩ =>
    if current_ctx.hasFinished then current_ctx
    else
      let h_neighbor_reachable : sys.reachable th postState :=
        EnumerableTransitionSystem.reachable.step curr postState h_curr ⟨tr, h_neighbor_in_tr⟩
      SearchContext.tryExploreNeighbor fpSt current_ctx ⟨tr, postState⟩ h_neighbor_reachable
  ) ctx

/-- Perform one step of BFS. -/
@[specialize]
def SearchContext.bfsStep {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [BEq ρ] [BEq σ] [BEq κ]
  [sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) κ (List (κ × σ))]
  {th : ρ} {hTh : th ∈ sys.theories}
  {params : SearchParameters ρ σ}
  (ctx : @SearchContext ρ σ κ σₕ List _ _ _ fp sys th hTh params) :
  @SearchContext ρ σ κ σₕ List _ _ _ fp sys th hTh params :=
  match ctx.sq.dequeue? with
  | none => { ctx with finished := StoppingCondition.exploredAllReachableStates }
  | some ((fpSt, curr), q_tail) =>
    have h_curr : sys.reachable th curr := sorry
    let ctx_dequeued : @SearchContext ρ σ κ σₕ List _ _ _ fp sys th hTh params := {
      ctx with
        sq := q_tail,
        queue_sound := sorry
        visited_sound := ctx.visited_sound
        queue_sub_visited := sorry
        queue_wellformed := sorry
    }
    SearchContext.processState fpSt curr h_curr ctx_dequeued


end Veil.ModelChecker.Concrete
