
import Veil.Basic

-- NOTE: if you change this, make sure you also change
-- `findStateType` in `Tactic/Util.lean`
class RelationalTransitionSystem (σ : Type) where
  init : σ → Prop
  assumptions : σ → Prop
  next : σ -> σ -> Prop
  safe : σ → Prop
  inv : σ → Prop

namespace RelationalTransitionSystem
open RelationalTransitionSystem

/-- All states in the invariant are safe. -/
def invSafe [RelationalTransitionSystem σ] :=
  ∀ (s : σ), assumptions s -> inv s -> safe s

/-- The set of initial states are in the invariant. -/
def invInit [RelationalTransitionSystem σ] :=
  ∀ (s : σ), assumptions s -> init s -> inv s

/-- The invariant is preserved by transition. -/
def invConsecution [RelationalTransitionSystem σ] :=
  ∀ (s1 s2 : σ), assumptions s1 -> inv s1 -> next s1 s2 -> inv s2

/-- The invariant is inductive. -/
def invInductive [sys: RelationalTransitionSystem σ] :=
  @invInit σ sys ∧ @invConsecution σ sys

end RelationalTransitionSystem

/--
  `σ` - state type
  `ρ` - return value of actions
-/
class AxiomaticTransitionSystem (σ : Type) where
  init : σ -> (σ → Prop) → Prop
  next : σ -> (σ → Prop) → Prop

  assumptions : σ → Prop
  safe : σ → Prop
  inv : σ → Prop

namespace AxiomaticTransitionSystem
open AxiomaticTransitionSystem

/-- All states in the invariant are safe. -/
def invSafe [sys : AxiomaticTransitionSystem σ] :=
  ∀ (s : σ), sys.assumptions s -> sys.inv s -> sys.safe s

/-- The set of initial states are in the invariant. -/
def invInit [sys : AxiomaticTransitionSystem σ] :=
  ∀ (s : σ), sys.assumptions s -> sys.init s sys.inv

/-- The invariant is preserved by transition. -/
def invConsecution [sys : AxiomaticTransitionSystem σ] :=
  ∀ (s : σ), sys.assumptions s -> sys.inv s -> sys.next s sys.inv

/-- The invariant is inductive. -/
def invInductive [sys : AxiomaticTransitionSystem σ] :=
  @invInit σ sys ∧ @invConsecution σ sys

end AxiomaticTransitionSystem
