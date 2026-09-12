import Veil.Core.Tools.ModelChecker.Interface
import Veil.Util.Histogram

namespace Veil.ModelChecker.Simulation
open Lean

structure SimulateConfig where
  maxTraces : Nat := 10000
  maxSteps : Nat := 100
  seed : Nat := 0
deriving Inhabited, Repr

inductive SimulationResult (ρ σ κ : Type) where
  | cancelled
  /-- The concrete theory is invalid, before any trace is attempted. -/
  | assumptionFailure (violates : List Name)
  | foundViolation (violation : ViolationKind) (viaTrace : Trace ρ σ κ)
deriving Inhabited, Repr

inductive SimulationTerminationReason where
  | noInitialStates
deriving Inhabited, Hashable, BEq, Repr

instance : ToJson SimulationTerminationReason where
  toJson
    | .noInitialStates => Json.mkObj [("kind", "no_initial_states")]

/-- An empty depth histogram for a run with the given per-trace step budget.
Depths range over `0 … maxSteps + 1`; the `+1` covers a failing assertion step. -/
def depthHistogramFor (maxSteps : Nat) : Histogram := Histogram.forRange (maxSteps + 2)

/--
The outcome of a `#simulate` run, together with the metadata reported to the user.

`SimulationResult` has no `noViolationFound` constructor: the absence of a
violation is encoded by the pair `(result, terminationReason)`.

| Situation              | `result`                    | `terminationReason`     |
| ---------------------- | --------------------------- | ----------------------- |
| Invalid theory         | `some (.assumptionFailure ..)` | `none`               |
| Violation found        | `some (.foundViolation ..)` | `none`                  |
| Cancelled              | `some .cancelled`           | `none`                  |
| Trace budget exhausted | `none`                      | `none`                  |
| No initial states      | `none`                      | `some .noInitialStates` |

The trace-budget-exhausted row is the only way to reach `result = none` with no reason, and it
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
  /-- Depths reached by the traces that ran. Empty for the pure entry points, which
  do not collect it. -/
  depthHistogram : Histogram := {}

end Veil.ModelChecker.Simulation
