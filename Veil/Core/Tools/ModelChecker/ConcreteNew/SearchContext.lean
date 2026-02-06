import Veil.Core.Tools.ModelChecker.ConcreteNew.Core
import Veil.Core.Tools.ModelChecker.Concrete.Subtypes
import Veil.Core.Tools.ModelChecker.Concrete.Containers

namespace Veil.ModelChecker.Concrete

abbrev SequentialSearchContext (σ κ σₕ : Type) [fp : StateFingerprint σ σₕ] [BEq κ] [Hashable κ] :=
  BaseSearchContext σ κ σₕ × fQueue (QueueItem σₕ σ)

-- TODO conjecture: executable things should not become part of this structure
-- (e.g., arguments), otherwise some reference counting will boom?
structure SequentialSearchContextInvariants {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (sctx : SequentialSearchContext σ κ σₕ)
extends @SearchContextInvariants ρ σ κ σₕ fp th sys params (· ∈ sctx.2) (· ∈ sctx.1.seen)
where
  -- NOTE: should be strengthened to talk about depth, with this
  -- being a special case
  init_states_included : ∀ s ∈ sys.initStates, (fp.view s) ∈ sctx.1.seen
  terminate_empty_queue : sctx.1.finished = some (.exploredAllReachableStates) → sctx.2.isEmpty
  stable_closed :  Function.Injective fp.view →
    (sctx.1.finished = some (.exploredAllReachableStates) ∨ sctx.1.finished = none) →
      ∀ u : σ, (fp.view u) ∈ sctx.1.seen →
        (∀ d : Nat, ⟨fp.view u, u, d⟩ ∉ sctx.2) →
          ∀ l v, (l, ExecutionOutcome.success v) ∈ sys.tr th u →
          (fp.view v) ∈ sctx.1.seen

end Veil.ModelChecker.Concrete
