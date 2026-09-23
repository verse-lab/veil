# Simulation proofs with CSLib

Veil uses CSLib's
[`LTS`](https://github.com/leanprover/cslib/blob/v4.32.0/Cslib/Foundations/Semantics/LTS/Basic.lean)
and
[`LTS.IsSimulation`](https://github.com/leanprover/cslib/blob/v4.32.0/Cslib/Foundations/Semantics/LTS/Simulation.lean)
directly. Import the bridge in files containing refinement proofs:

```lean
import Veil.CSLib.Simulation
```

For a specification whose `#gen_spec` has generated `relationalTransitionSystem`,
its CSLib system is simply:

```lean
relationalTransitionSystem.toLTS th
```

The adapter fixes the background theory `th` and uses the existing `tr` relation
unchanged. No additional generation command or separately generated definition
is needed. These are the successful transitions used by Veil's reachable-state
invariants.

## Reachability and invariants

CSLib's `LTS` contains a transition relation, but no background assumptions or
initial-state predicate. The bridge proves the exact correspondence:

```lean
sys.reachable th s ↔ sys.assumptions th ∧
  ∃ s₀, sys.init th s₀ ∧ (sys.toLTS th).CanReach s₀ s
```

`RelationalTransitionSystem.reachable_of_simulation` combines an ordinary CSLib
simulation with proofs that assumptions and initial states correspond.
`invariant_of_simulation` additionally takes an abstract invariant and a proof
that the state relation transfers it to the concrete property. A generated
`Abstract.safe.is_inv thAbstract` can supply the abstract invariant directly.

Both theories are fixed independently. For a theory map, apply the theorem at
`thConcrete` and `mapTheory thConcrete`. This also supports choosing an abstract
state type after fixing the concrete theory, as the dissertation's ring proof
does with `{n : Nat // n ∈ th.allNodes}`.

## Stuttering and different labels

CSLib's `IsSimulation` matches each concrete edge with one abstract edge with
the **same label**. The dissertation's `PointedForwardSimulation` instead permits
zero or more abstract steps and different label types.

To express that behavior using the same CSLib definition, make the target a
CSLib LTS whose edges represent finite abstract executions. For example:

```lean
def abstractPaths (sys : Veil.RelationalTransitionSystem ρa σa la) (th : ρa) :
    Cslib.LTS σa lc where
  Tr sa _ sa' := (sys.toLTS th).CanReach sa sa'
```

Then prove `Cslib.LTS.IsSimulation (concrete.toLTS thConcrete)
(abstractPaths abstract thAbstract) rel`. An empty path witnesses stuttering;
CSLib's `MTr` witnesses a longer execution. This ignores action labels, exactly
as the dissertation's unlabelled forward simulation does.

Use `reachable_of_simulation_into` or `invariant_of_simulation_into` for this
case. Their additional `hsteps` premise requires that every target edge is a
real finite execution of the abstract system. For `abstractPaths` above this
proof is `fun _ _ _ h => h`. For trace-sensitive refinement, the target relation
can instead constrain which abstract label sequence matches each concrete label.
CSLib's own saturation operations can likewise be used with a proof of `hsteps`.
The closure encoding establishes safety refinement; it does not assert progress
or preservation of infinite executions.

See [the checked examples](../VeilTest/CSLibSimulation.lean) for direct simulation,
stuttering, a concrete step matching two abstract steps, transfer of a generated
invariant, and a theory-dependent abstract state type. No Veil-specific simulation
predicate is introduced.

The [Ring refinement example](../Examples/Ring/README.md) ports the full
dissertation simulation proof to this interface and derives the concrete
single-leader safety theorem from the abstract generated invariant.

## Imports and versions

The dependency is pinned to CSLib `v4.32.0` (commit
`197a7be621263b84c67ca4f803f69205b36d06df`), which uses the same Lean toolchain
as Veil. Veil keeps its standalone Loom dependency; CSLib brings Mathlib as a
transitive package dependency. The bridge imports
`Cslib.Foundations.Semantics.LTS.Simulation`, not the umbrella `Cslib` module.
For just the adapter and reachability correspondence, import
`Veil.CSLib.TransitionSystem` instead.

These modules are opt-in: importing `Veil` imports neither CSLib nor Mathlib.
CSLib's leaf modules do have transitive Mathlib imports, and Lake still resolves
the package dependencies. Lean's module system limits imports; it does not remove
those transitive dependencies. In a file using `module`, use `public import` for
the bridge when exporting declarations that depend on it.
