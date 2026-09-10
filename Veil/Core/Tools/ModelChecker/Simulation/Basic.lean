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

/--
The outcome of a `#simulate` run, together with the metadata reported to the user.

`SimulationResult` has no `noViolationFound` constructor: the absence of a
violation is encoded by the pair `(result, terminationReason)`.

| Situation              | `result`                    | `terminationReason`     |
| ---------------------- | --------------------------- | ----------------------- |
| Violation found        | `some (.foundViolation ..)` | `none`                  |
| Cancelled              | `some .cancelled`           | `none`                  |
| Trace budget exhausted | `none`                      | `none`                  |
| No initial states      | `none`                      | `some .noInitialStates` |

The third row is the only way to reach `result = none` with no reason, and it
always comes with `tracesRun = maxTraces`. It is the simulation counterpart of
the model checker terminating early on a bound, but it needs no payload beyond
`tracesRun`, so it is left implicit rather than named in
`SimulationTerminationReason`.
-/
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
