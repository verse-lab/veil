import Veil.Core.Tools.ModelChecker.ConcreteNew.Core
import Veil.Core.Tools.ModelChecker.Concrete.Subtypes
import Veil.Core.Tools.ModelChecker.Concrete.Containers

namespace Veil.ModelChecker.Concrete

section Sequential

abbrev SequentialSearchContext (σ κ σₕ : Type) [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] :=
  BaseSearchContext σ κ σₕ × fQueue (QueueItem σₕ σ)

variable {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)

/-- A sequential search context is stable closed if for any state `u` that
has been seen and has been fully processed (i.e., not in the queue, not being
processed), then all its successfully reachable have also been seen. -/
abbrev SequentialSearchContext.isStableClosed (sctx : SequentialSearchContext σ κ σₕ)
  -- (Optional) state that is currently being processed
  (stateInTransit : Option σ) : Prop :=
  Function.Injective fp.view →
    (sctx.1.finished = some (.exploredAllReachableStates) ∨ sctx.1.finished = none) →
      ∀ u ∉ stateInTransit, (fp.view u) ∈ sctx.1.log →
        (∀ d : Nat, ⟨fp.view u, u, d⟩ ∉ sctx.2) →
          ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th u →
            (fp.view v) ∈ sctx.1.log

-- TODO conjecture: executable things should not become part of this structure
-- (e.g., arguments), otherwise some reference counting will boom?
structure SequentialSearchContextInvariants
  (stateInTransit : Option σ)
  (sctx : SequentialSearchContext σ κ σₕ)
extends @SearchContextInvariants ρ σ κ σₕ fp th sys params (· ∈ sctx.2) (· ∈ sctx.1.log)
where
  -- NOTE: should be strengthened to talk about depth, with this
  -- being a special case
  init_states_included : ∀ s ∈ sys.initStates, (fp.view s) ∈ sctx.1.log
  terminate_empty_queue : sctx.1.finished = some (.exploredAllReachableStates) → sctx.2.isEmpty
  stable_closed : sctx.isStableClosed sys stateInTransit

abbrev LawfulSequentialSearchContext (stateInTransit : Option σ := .none) : Type :=
  Subtype (α := SequentialSearchContext σ κ σₕ) (SequentialSearchContextInvariants sys params stateInTransit)

/-- When finishing processing a state, we move from having that state `curr`
in transit to having no state in transit, provided that all successfully
reachable neighbors of `curr` in transit have been seen. -/
theorem SequentialSearchContextInvariants.finish_stateInTransit
  {sctx : SequentialSearchContext σ κ σₕ}
  {curr : σ}
  (sctx_invs : SequentialSearchContextInvariants sys params (.some curr) sctx)
  (h_neighbors_seen : ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th curr →
    (fp.view v) ∈ sctx.1.log) :
  SequentialSearchContextInvariants sys params .none sctx := by
  rcases sctx with ⟨ctx, sq⟩ ; rcases sctx_invs with ⟨h1, h2, h3, h_closed⟩ ; dsimp only at *
  constructor <;> try assumption
  simp [SequentialSearchContext.isStableClosed] at h_closed ⊢
  intro ha hb u hc hd l v hin
  by_cases heq : curr = u
  on_goal 2=> grind
  subst u ; eapply h_neighbors_seen ; assumption

end Sequential

section MapReduce

-- FIXME: The depth information in `QueueItem` is more or less useless here

/-
structure MapReduceSearchContextMain (σ κ σₕ : Type) [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] where
  base : BaseSearchContext σ κ σₕ
  -- CHECK I strongly suspect there is some bad memory usage here ...
  /-- Recording the nodes to visit in the next depth as an Array for efficient iteration/splitting. -/
  tovisitQueue : Array (QueueItem σₕ σ)
  /-- HashSet for O(1) membership checking of fingerprints in the queue. -/
  tovisitSet : Std.HashSet σₕ
-/

abbrev MapReduceSearchContextMain (σ κ σₕ : Type) [fp : StateFingerprint σ σₕ] [Ord σₕ] [BEq κ] [Hashable κ] :=
  BaseSearchContext σ κ σₕ × Array (QueueItem σₕ σ) × Std.TreeSet σₕ

abbrev MapReduceSearchContextLocal (σ κ σₕ : Type) [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] :=
  BaseSearchContext σ κ σₕ × Array (QueueItem σₕ σ)

variable {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)

-- structure MapReduceSearchContextMainInvariants
--   (mmctx : MapReduceSearchContextMain σ κ σₕ)
-- extends @SearchContextInvariants ρ σ κ σₕ fp th sys params (· ∈ mmctx.tovisitQueue) (· ∈ mmctx.base.log)
-- where
  -- tovisitConsistent : ∀ h, h ∈ tovisitSet ↔ ∃ item ∈ tovisitQueue, item.fingerprint = h

end MapReduce

end Veil.ModelChecker.Concrete
