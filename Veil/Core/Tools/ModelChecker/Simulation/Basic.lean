import Veil.Core.Tools.ModelChecker.Interface

namespace Veil.ModelChecker.Simulation
open Lean

structure SimulateConfig where
  maxTraces : Nat := 10000
  maxSteps : Nat := 100
  seed : Nat := 0
deriving Inhabited, Repr

inductive SimulationResult (ρ σ κ : Type) where
  | cancelled
  | foundViolation (violation : ViolationKind) (viaTrace : Trace ρ σ κ)
deriving Inhabited, Repr

def SimulationResult.depth {ρ σ κ : Type} : SimulationResult ρ σ κ → Nat
  | .foundViolation _ trace => trace.steps.size + if trace.failingStep.isSome then 1 else 0
  | .cancelled => 0

inductive SimulationTerminationReason where
  | noInitialStates
deriving Inhabited, Hashable, BEq, Repr

instance : ToJson SimulationTerminationReason where
  toJson
    | .noInitialStates => Json.mkObj [("kind", "no_initial_states")]

structure SimulateResult (ρ σ κ : Type) where
  result : Option (SimulationResult ρ σ κ)
  tracesRun : Nat
  maxTraces : Nat
  elapsedMs : Nat
  seed : Nat
  terminationReason : Option SimulationTerminationReason := none

def SimulateResult.depth {ρ σ κ : Type} (result : SimulateResult ρ σ κ) : Nat :=
  match result.result with
  | some result => result.depth
  | none => 0

end Veil.ModelChecker.Simulation
