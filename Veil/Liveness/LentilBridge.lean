module

public import Lentil
public import Veil.Frontend.DSL.Action.Semantics.Definitions
public import Veil.Frontend.DSL.Infra.Simp

public section

namespace Veil.Liveness

variable {ρ σ l : Type}

@[enabledSimp ↓]
theorem enabled_bridging (tr : Transition ρ σ) (th : ρ) :
  (Enabled (tr th)) =tl= (⌜ tr.enabled th ⌝) := rfl

@[enabledSimp ↓]
theorem enabled_bridging' (tr : Transition ρ σ) (th : ρ) (st : σ) :
  Lentil.enabled (tr th) st = tr.enabled th st := rfl

end Veil.Liveness
