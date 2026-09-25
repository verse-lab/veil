# Simulation proofs with CSLib

The optional [VeilExtra package](../VeilExtra/README.md) uses CSLib's
[`LTS`](https://github.com/leanprover/cslib/blob/v4.32.0/Cslib/Foundations/Semantics/LTS/Basic.lean)
and
[`LTS.IsSimulation`](https://github.com/leanprover/cslib/blob/v4.32.0/Cslib/Foundations/Semantics/LTS/Simulation.lean)
directly. Build it from the repository root with `lake -d VeilExtra build`.
In files inside that package, import the bridge for refinement proofs:

```lean
import VeilExtra.CSLib.Simulation
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

## Internal actions and weak simulation

For weak simulation, import:

```lean
import VeilExtra.CSLib.WeakSimulation
```

Choose a common observation type with an instance of `Cslib.HasTau`, whose `τ`
value denotes an internal action. Map each system's native labels into that type:

```lean
concrete.toObservedLTS thConcrete observeConcrete
abstract.toObservedLTS thAbstract observeAbstract
```

The native label types can differ. Several native labels can have the same
observation; for example, both `prepare` and `cleanup` can map to `τ`. An observed
transition exists exactly when a native transition has the given observation.
This adapter is needed because CSLib's `mapLabel` pulls labels back in the
opposite direction.

Prove the ordinary CSLib simulation predicate with a saturated abstract target:

```lean
Cslib.LTS.IsSimulation
  (concrete.toObservedLTS thConcrete observeConcrete)
  (abstract.toObservedLTS thAbstract observeAbstract).saturate rel
```

CSLib's [`STr` and `saturate`](https://github.com/leanprover/cslib/blob/v4.32.0/Cslib/Foundations/Semantics/LTS/HasTau.lean)
give the target edges their meaning:

- A `τ` edge represents any finite sequence of internal actions, including none.
- A visible `a` edge represents `τ*; a; τ*`: exactly one action observed as `a`,
  with any finite number of internal actions before and after it.

A visible event cannot be matched by an empty execution, a different event, or
two visible events. The matching action can still leave the state unchanged.
The underlying `STr.refl`, `STr.single`, and `STr.tr` constructors supply proof
witnesses directly; Veil introduces no separate weak-simulation predicate.

`reachable_of_weakSimulation` and `invariant_of_weakSimulation` combine this
simulation with background-assumption and initialization proofs. They discharge
the correspondence with native finite executions automatically, so generated
`<clause>.is_inv` theorems can be transferred as before.

CSLib's `hsim.isSimulation_saturate_left` derives a simulation with **both**
systems saturated. Its `hsim.sim_trace` matches finite observed traces in the
saturated target. `observed_mTr_of_mTr` turns a native trace into an observed one.

This is more expressive about observations than unlabelled path matching, while
imposing stronger obligations when actions remain visible. Hiding **every**
action recovers exactly arbitrary finite-path matching, as proved by
`all_internal_sTr_iff_canReach`. These are finite-execution results: they do not
establish fairness, eventual progress, or divergence-sensitive refinement.

### Ring example

The [Ring refinement](../VeilExtra/VeilExtra/Examples/Ring/README.md) uses this interface:

- `send` is internal (`τ`), and `recv` is the visible `receive` event.
- A duplicate concrete send matches zero abstract steps.
- Most steps match one abstract action.
- A leader receiving its own token again matches abstract `recv; send`: one
  visible receive followed by an internal send.

The observation records the action kind, not the receive parameters. The state
relation still connects leaders and pending messages, and transports the abstract
generated single-leader invariant to the concrete system.

## Other finite-path matching policies

`reachable_of_simulation_into` and `invariant_of_simulation_into` remain available
for arbitrary target LTSs. Their `hsteps` premise requires each target edge to
represent a real finite abstract execution. For example, the dissertation's
unlabelled `PointedForwardSimulation` can also be encoded directly as:

```lean
def abstractPaths (sys : Veil.RelationalTransitionSystem ρa σa la) (th : ρa) :
    Cslib.LTS σa lc where
  Tr sa _ sa' := (sys.toLTS th).CanReach sa sa'
```

Here `hsteps` is `fun _ _ _ h => h`, and labels are ignored. Each concrete step
can match any finite abstract execution, including zero or multiple steps.

## Imports and versions

The dependency is pinned to CSLib `v4.32.0` (commit
`197a7be621263b84c67ca4f803f69205b36d06df`), which uses the same Lean toolchain
as Veil. Core Veil keeps its standalone Loom dependency and does not depend on
CSLib or Mathlib. VeilExtra depends on the parent Veil checkout and CSLib;
Mathlib is a transitive dependency of VeilExtra only. The bridge imports
`Cslib.Foundations.Semantics.LTS.Simulation`, not the umbrella `Cslib` module.
For just the adapter and reachability correspondence, import
`VeilExtra.CSLib.TransitionSystem` instead.

Core `lake build` and `import Veil` use neither CSLib nor Mathlib. VeilExtra has
its own Lake manifest, dependency directory, and CI builds. Merely separating
Lean libraries within the root package would not isolate those dependencies.
CSLib's leaf modules still have transitive Mathlib imports inside VeilExtra.
In a file using `module`, use `public import` for the bridge when exporting
declarations that depend on it.
