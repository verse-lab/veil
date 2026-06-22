import Lentil
import Veil.Frontend.DSL.Action.Semantics.Definitions
import Veil.Frontend.DSL.Infra.Simp

namespace Veil.Liveness

variable {ρ σ l : Type}

@[enabledSimp ↓]
theorem enabled_bridging (tr : Transition ρ σ) (th : ρ) :
  (Enabled (tr th)) =tla= (⌜ tr.enabled th ⌝) := rfl

@[enabledSimp ↓]
theorem enabled_bridging' (tr : Transition ρ σ) (th : ρ) (st : σ) :
  TLA.enabled (tr th) st = tr.enabled th st := rfl

end Veil.Liveness
