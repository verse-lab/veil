module

public import Veil.Frontend.DSL.Action.Semantics.Theorems
public import Veil.Frontend.DSL.Action.Semantics.WP

public section

open Loom.Order
open scoped Loom.Order

namespace Veil

/-- Executing a native transition can restrict its possible steps to those
representable through the state lens; every successful step still satisfies
the original two-state relation. Equality is not required. -/
theorem Transition.toVeilM_toTransitionDerived_sound
    {m : Mode} {ρ small big : Type} [lens : IsSubStateOf small big]
    (tr : Transition ρ big) (th : ρ) (before after : big)
    (step : (Transition.toVeilM (m := m) (σ := small) tr).toTransitionDerived th before after) :
    tr th before after := by
  classical
  simp [VeilM.toTransitionDerived, VeilSpecM.toTransitionDerived, Transition.toVeilM,
    Loom.Cont.inv, Loom.Order.compl, wpSimp] at step
  grind

end Veil
