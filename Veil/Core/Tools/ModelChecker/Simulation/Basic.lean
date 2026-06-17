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
  depth : Nat
  terminationReason : Option SimulationTerminationReason := none

end Veil.ModelChecker.Simulation
