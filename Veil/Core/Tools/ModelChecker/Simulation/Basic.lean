import Veil.Core.Tools.ModelChecker.Interface

namespace Veil.ModelChecker.Simulation

structure SimulateConfig where
  maxTraces : Nat := 10000
  maxSteps : Nat := 100
  seed : Nat := 0
deriving Inhabited, Repr

inductive SimulationResult (ρ σ κ : Type) where
  | cancelled
  | foundViolation (violation : ViolationKind) (viaTrace : Trace ρ σ κ)
deriving Inhabited, Repr

structure SimulateResult (ρ σ κ : Type) where
  result : Option (SimulationResult ρ σ κ)
  tracesRun : Nat
  maxTraces : Nat
  elapsedMs : Nat
  seed : Nat
  depth : Nat

@[inline]
def restrictSystemByStateConstraints {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) :
  EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀ :=
  if params.stateConstraints.isEmpty then sys else {
    initStates := sys.initStates.filter (params.satisfiesConstraints th)
    tr := fun th' st => (sys.tr th' st).filter fun (_, outcome) =>
      match outcome with
      | .success st' => params.satisfiesConstraints th st'
      | .assertionFailure _ st' => params.satisfiesConstraints th st'
      | .divergence => true
  }

end Veil.ModelChecker.Simulation
