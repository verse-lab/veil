import Veil.Core.Tools.ModelChecker.Concrete.DataStructures
import Veil.Core.Tools.ModelChecker.TransitionSystem

namespace Veil.ModelChecker.Concrete

/-- A function that maps a full state to a view of the state. -/
class StateView (FullState View : Type) where
  view : FullState → View

@[default_instance low] instance : StateView σ σ where
  view := id

class abbrev StateFingerprint (FullState View : Type) := BEq View, Hashable View, StateView FullState View

/-- A model checker search context is parametrised by the system that's being
checked and the theory it's being checked under. -/
structure SearchContext
  [Collection ρSet ρ] [Collection σSet σ] [Collection nextSet (κ × σ)]
  [sys : ExecutableTransitionSystem ρ ρSet σ σSet κ nextSet]
  [fp : StateFingerprint σ σₕ]
  (th : ρ)
where
  seen  : Std.HashSet σₕ
  sq    : fQueue (σₕ × σ)
  /- We use a `HashMap σ_post (σ_pre × κ)` to store the log of transitions, which
  will make it easier to reconstruct counterexample trace. -/
  log                : Std.HashMap σₕ (σₕ × κ)
  counterexample     : List σₕ
  termination        : Bool
  queue_sound        : ∀ x : σ, ⟨fp.view x, x⟩ ∈ fQueue.toList sq → sys.reachable th x
  visited_sound      : Function.Injective fp.view → ∀ x, (fp.view x) ∈ seen → sys.reachable th x
  queue_sub_visited  : ∀ x : σ, ⟨fp.view x, x⟩ ∈ fQueue.toList sq → (fp.view x) ∈ seen
  queue_wellformed   : ∀ fingerprint st, ⟨fingerprint, st⟩ ∈ fQueue.toList sq → fingerprint = fp.view st


end Veil.ModelChecker.Concrete
