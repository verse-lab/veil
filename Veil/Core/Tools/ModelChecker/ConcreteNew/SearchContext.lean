import Veil.Core.Tools.ModelChecker.ConcreteNew.Core
import Veil.Core.Tools.ModelChecker.Concrete.Subtypes
import Veil.Core.Tools.ModelChecker.Concrete.Containers

namespace Veil.ModelChecker.Concrete

-- TODO conjecture: executable things should not become part of this structure
-- (e.g., arguments), otherwise some reference counting will boom?
structure SequentialSearchContextInvariants {ρ σ κ σₕ : Type}
  [fp : StateFingerprint σ σₕ]
  [instBEq : BEq κ] [instHash : Hashable κ]
  {th : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th)
  (params : SearchParameters ρ σ)
  (sq    : fQueue (QueueItem σₕ σ))
  (ctx   : BaseSearchContext σ κ σₕ)
extends @SearchContextInvariants ρ σ κ σₕ fp th sys params (· ∈ sq) (· ∈ ctx.seen)
where
  terminate_empty_queue : ctx.finished = some (.exploredAllReachableStates) → sq.isEmpty
  stable_closed :  Function.Injective fp.view →
    (ctx.finished = some (.exploredAllReachableStates) ∨ ctx.finished = none)
      → ∀ u : σ, (fp.view u) ∈ ctx.seen → (∀ d : Nat, ⟨fp.view u, u, d⟩ ∉ sq) →
      ∀l v, (l, ExecutionOutcome.success v) ∈ sys.tr th u → (fp.view v) ∈ ctx.seen

end Veil.ModelChecker.Concrete
