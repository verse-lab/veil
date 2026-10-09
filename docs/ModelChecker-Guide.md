# Veil Model Checker Guide

`#model_check` explores every reachable state of a finite instance of a Veil
module and checks each `safety` and `invariant` clause in every state it
reaches. This guide covers running the checker, reading its results, and
keeping searches small and fast. The specification language itself is
described in [DSL-Reference.md](DSL-Reference.md).

## Running the Checker

```lean
#model_check { node := Fin 3 } { leader := 0 }
```

The first argument instantiates the module's types and `param`s; the second
gives concrete values for its theory (`immutable` fields). The theory can be
omitted when the module has none, but must be written (as `{}`) whenever
options follow, or the first option is parsed as the theory.

Type arguments that follow from the module's `instantiate` constraints can be
left as holes. With `instantiate nset : TSet node nodeSet`, the element type of
the container is determined by `node`, so `nodeSet := OrdList _` suffices, and
a bare `nodeSet := _` picks Veil's default container for that class. Holes are
filled through `@[default_instance]`: Veil's own containers (`TSet`,
`TMultiset`, `TMap`) are covered, while instances of your own classes need the
attribute to take part.

```lean
#model_check { node := Fin 3, nodeSet := OrdList _ }
```

`#model_check` runs whenever the file is elaborated, including during
`lake build`. To check that a module can be executed without starting a search,
use `#gen_executable`.

### Execution Modes

| Command | Behavior |
| --- | --- |
| `#model_check` | Starts in the interpreter and compiles the model in the background; once the binary is ready (and no violation has been found yet), the search restarts with it |
| `#model_check interpreted` | Interpreter only; best for small instances |
| `#model_check compiled` | Compiled binary only |

### Options

Options follow the theory, e.g.
`#model_check { node := Fin 3 } {} (maxDepth := 5) (sequential := true)`.

| Option | Default | Effect |
| --- | --- | --- |
| `maxDepth` | `0` (no bound) | Stops after this many transitions from the initial states; the search is then incomplete |
| `sequential` | `false` | Runs a single-threaded search instead of the parallel one |
| `parallelCfg` | one subtask per core | Tunes the parallel search (`numSubTasks`, `thresholdToParallel`, `numSubSteps`) |
| `fingerprintType` | `Nat` | Type of the stored state fingerprints; `UInt64` keeps the full hash but uses more memory |
| `seenSet` | `TreeSetShard` | Set type of the parallel search's seen-set shards; `HAMTShard` and `HAMTKeysShard` are faster but use more memory per state |

The `#model_check` docstring describes `fingerprintType` and `seenSet` in
detail.

### Theory Assumptions

Before exploring, the checker evaluates the module's `assumption`s on the given
theory, and reports an `assumption_failure` without searching if one fails.
Append `assumptions_hold_by <tactic>` to also prove them at elaboration time.

The checker tests only the instance and theory you provide. It does not
enumerate other theories or type-class instances, so a passing run is a test,
not a proof.

## Reading the Result

| Output | Meaning |
| --- | --- |
| `✅ No violation (explored N states)` | No violation in the N distinct states reached. This covers every reachable state only if no `maxDepth` was set: a depth-bounded search prints the same message |
| `❌ Violation: safety_failure (violates: p)` | A reachable state violates `p`; the trace leads to it from an initial state |
| `❌ Violation: deadlock` | A reachable state has no successors and does not satisfy `termination` (see below) |
| `❌ Violation: assertion_failure` | An `assert` failed, or a `require` failed in a called procedure |
| `❌ Violation: assumption_failure (violates: a)` | The theory violates assumption `a`; nothing was explored |

The search stops at the first violation. Progress and action-coverage
statistics are shown live in the InfoView widget.

## Deadlocks and Termination

A reachable state without successors is reported as a deadlock unless it
satisfies the module's `termination` clause:

```lean
termination [allDone] ∀ p, done p
```

Without a `termination` clause, any state may stop, so no deadlock is ever
reported; write `termination false` to report every state without successors.
*Only the first `termination` clause is used.* It affects deadlock reporting
only: it adds no transitions and does not check that the system eventually
terminates.

## State Constraints

```lean
state_constraint [bounded] msgCount ≤ 5
```

A state that violates a `state_constraint` is dropped as soon as it is
generated: it is not counted, not checked against invariants, and not
expanded. A state whose successors are all dropped therefore has no successors,
and is reported as a deadlock unless `termination` holds in it.

## Set-Valued State

Declare a set-valued field through a carrier type that implements `TSet`, and
pick the carrier when instantiating:

```lean
type node
type nodeSet
instantiate nodes : TSet node nodeSet
individual pending : nodeSet

-- ...

#model_check { node := Fin 3, nodeSet := Std.ExtTreeSet (Fin 3) } {}
```

`TSet` provides membership (`∈`, `contains`), `empty`, `isEmpty`, `insert`,
`remove`, `union`, `diff`, `intersection`, `filter`, `map`, `filterMap`,
`count`, `ofList`/`toList`, `subsets`, and `TSet.isSubset`. Carriers include
`Std.ExtTreeSet`, `OrdList`, and `OrdArray`. `TMultiset` (carrier
`TMapMultiset`) has the same membership interface and also counts
multiplicities; use it only when multiplicity matters.

Choices over sets enumerate only what they need: `{ x // x ∈ s }` ranges over
the elements of `s`, and `{ t // TSet.isSubset t s }` over the subsets of `s`.
Use these types with `pick` and `:|` instead of ranging over a whole type.

## Field Representations

By default, relation fields are stored as `Std.ExtTreeSet`s and function fields
as `Std.ExtTreeMap`s. `veil_set_field_representation` changes this for all
relation fields or all function fields of a module, and must come before
`#gen_state`:

```lean
veil_set_field_representation relation Veil.ArrayAsFinset
veil_set_field_representation function Veil.ArrayAsFinmap
```

| Representation (relation / function) | Notes |
| --- | --- |
| `Std.ExtTreeSet` / `Std.ExtTreeMap` | Default |
| `Veil.ArrayAsFinset` / `Veil.ArrayAsFinmap` | Dense arrays over a `FinEncodable` domain; suit small domains, but large product domains make every state big |
| `Veil.BitVecAsFinset` / `Veil.BitVecAsFinmap` | Packed bit vectors; the map version also needs a finitely encodable codomain |
| `Veil.CanonicalField` | Plain functions; a simple baseline |

For a custom array index type, derive `Veil.FinEncodable` directly:

```lean
inductive Key (node : Type) where
  | local (n : node)
  | pair (src dst : node)
  | global
deriving Veil.FinEncodable
```

`Key node` requires `[Veil.FinEncodable node]`. Deriving also supports structures
and empty types; recursive and indexed inductives are unsupported. Non-deterministic choices and
field updates still need `Enumeration`.

A representation changes how states are stored, not which states are
reachable, so the explored-state count stays the same. It does not affect
`TSet` carriers. See `VeilTest/SetFieldRepresentation.lean` for examples.

## Constant Functions and Relations

A function or relation that never changes, such as quorum membership in Paxos,
can be declared in three ways:

```lean
immutable relation member (a : acceptor) (q : quorum)  -- theory field
param member : acceptor → quorum → Bool                -- module parameter
instantiate pm : PaxosMember acceptor quorum           -- type-class field
```

The compiled checker treats them differently. An `immutable` field is part of
the theory value, which the checker receives at run time: actions read it from
the theory and call it through a closure, which the compiler can neither
inline nor simplify. A `param` or a type-class field is a parameter of the
module's definitions that is fixed when `#model_check` is elaborated, so the
generated code calls the concrete function directly. A condition built only
from such constants, with no state and no action parameter in it, e.g.
`∀ q1 q2, ∃ a, member a q1 ∧ member a q2` where `member` is a constant, is then evaluated once for the whole
search instead of once per state.

When actions and invariants evaluate the constant many times per state, as
Paxos does in `∀ a, member a Q → …`, calling the constant through closures costs more search time.
The gap is larger when a `require`, invariant, or `state_constraint` mentions
only constants, since `immutable` re-evaluates that condition in every state.

Prefer `param` for a plain constant and `instantiate` for one that comes with
assumptions (see [DSL-Reference.md](DSL-Reference.md)); `assumption`s may refer
to either. This only concerns the model checker: for verification, all three
are uninterpreted symbols constrained by the module's assumptions.

For quorums in particular, `Veil/Frontend/Std.lean` provides `Quorum α` (every
majority of `α`) and `MinQuorum α` (the majorities of minimal size) as bit-vector sets, with `a ∈ q` as membership
and the usual set-like notation (e.g., `{0, 1}`) as display. 

## Keeping Searches Small and Fast

- Start with `#model_check interpreted` on the smallest interesting instance;
  use the default mode for larger ones.
- Choose from the actual collection (`{ x // x ∈ s }`) rather than a whole
  type, and prefer `let x :| P` over `pick` followed by `assume`.
- Prefer imperative actions to `transition`s, which are much slower to execute.
- Declare constant functions and relations as `param`s or type-class fields
  rather than `immutable` components (see above).
- Bound otherwise unbounded models with `state_constraint`.
- When time or memory is the bottleneck, try other field representations,
  `fingerprintType`, or `seenSet`. Compare settings on the same instance and
  machine, separate compilation time from search time, and check that the
  explored-state count does not change.
- If exhaustive search is out of reach, `#simulate` runs random walks instead
  (see [DSL-Reference.md](DSL-Reference.md)).
