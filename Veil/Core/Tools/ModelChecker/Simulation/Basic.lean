import Veil.Core.Tools.ModelChecker.Interface

namespace Veil.ModelChecker.Simulation

structure SimulateConfig where
  maxTraces : Nat := 10000
  maxSteps : Nat := 100
  seed : Nat := 0
deriving Inhabited, Repr

structure SimulateResult (ρ σ κ : Type) where
  result : ModelCheckingResult ρ σ κ Unit
  tracesRun : Nat
  elapsedMs : Nat
  seed : Nat
  depth : Nat

@[inline]
def violatedInvariantNames {ρ σ : Type}
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) : List Lean.Name :=
  params.invariants.filterMap fun p =>
    if !p.holdsOn th st then some p.name else none

@[inline]
def filterInitStatesByConstraints {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) : List σ :=
  if params.stateConstraints.isEmpty then sys.initStates
  else sys.initStates.filter (params.satisfiesConstraints th)

@[inline]
def filterOutcomesByConstraints {ρ σ κ : Type} {th₀ : ρ}
  (sys : EnumerableTransitionSystem ρ (List ρ) σ (List σ) Int κ (List (κ × ExecutionOutcome Int σ)) th₀)
  (params : SearchParameters ρ σ) (th : ρ) (st : σ) : List (κ × ExecutionOutcome Int σ) :=
  if params.stateConstraints.isEmpty then
    sys.tr th st
  else
    (sys.tr th st).filter fun (_, outcome) =>
      match outcome with
      | .success st' => params.satisfiesConstraints th st'
      | .assertionFailure _ st' => params.satisfiesConstraints th st'
      | .divergence => true

end Veil.ModelChecker.Simulation
