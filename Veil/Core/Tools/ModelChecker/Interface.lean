import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.ModelChecker.Trace

namespace Veil.ModelChecker
open Lean Trace


structure SafetyProperty (ρ σ : Type) where
  name : Name
  property : ρ → σ → Prop

def SafetyProperty.holds (p : SafetyProperty ρ σ) (th : ρ) (st : σ) [Decidable (p.property th st)] : Prop :=
  decide (p.property th st)

inductive ReachabilityResult where
  | reachable (viaTrace : Option (Trace ρ σ l))
  | unreachable
  | unknown
deriving Inhabited

class ModelChecker (ts : TransitionSystem ρ σ l) where
  isReachable : SafetyProperty ρ σ → ReachabilityResult

end Veil.ModelChecker
