# Veil DSL Reference

A Veil module specifies a **state transition system**, describing:

- the type of the background theory the system assumes
- the type of the state the system operates on

Every Veil module follows a canonical structure with the following components:

1. Module declaration
2. Type declarations
3. Type class instance declarations
4. State and theory components (individuals, relations, functions)
    - the state consists of the mutable components
    - the background theory consists of the `immutable` components
5. State generation via `#gen_state`
6. Ghost relations (to aid specification)
7. Initial state
8. Procedures, actions, and transitions
    - procedures are internal helper routines that can be called from actions
    - actions are externally visible transitions that the environment can invoke
    - transitions are two-state relations; an alternative, relational way of
      specifying what actions specify imperatively
9. Properties (safety, invariants, assumptions, temporal properties)
10. Specification generation & verification commands

### 1. Module Declaration

A Veil module begins with `veil module <Name>` and ends with `end <Name>`:

```lean
module

public import Veil

veil module Ring
-- module contents go here
end Ring
```

The `module` header enables Lean’s module system and must precede the imports.
The `public import Veil` statement brings in all Veil DSL syntax and utilities. It must be public
because a model exports generated declarations whose types and bodies refer to Veil definitions.
Verification tools are imported for elaboration only; compiled model checkers link the runtime dependencies.
`veil module` sets the visibility and transparency of its declarations automatically;
users do not need a `public section` or `@[expose]` annotation.

### 2. Type Declarations

Veil supports several kinds of type declarations:

#### Uninterpreted Types

Abstract types with no internal structure:

```lean
type node
type round
type value
```

When _verifying_ a module, Veil universally quantifies over its type
parameters, i.e. it checks that the system is correct for **all** types that
satisfy the stated assumptions. When _model checking_, you provide a concrete
instantiation for each of them (e.g. `node := Fin 4`).

#### Parameters

`type` is a special case of the more general `param` command, which declares a
parameter of arbitrary type (`type node` is equivalent to `param node : Type`
plus auto-generated `DecidableEq` and `Inhabited` instances):

```lean
param n : Nat
param m : Fin n   -- dependent parameters are allowed
```

#### Enumerated Types

Types with a finite set of constructors:

```lean
enum color = {red, blue, green}
enum pc_state = {idle, waiting, critical}
```

#### Lean Structures

For complex data types, use the `@[veil_decl]` attribute:

```lean
@[veil_decl] structure Message (node : Type) where
  payload : node
  src : node
  dst : node
```

This marks the structure for use within Veil's verification framework.

### 3. Type Class Instantiation

Veil provides standard type classes for common structures.
Use `instantiate` to introduce them:

```lean
instantiate tot : TotalOrder node
instantiate btwn : Between node
open Between TotalOrder
```

The `open` command makes the type class fields available without qualification.

See `Std.lean` for the complete list of type classes.

### 4. State and Theory Components

State components define the **signature** of your transition system.
There are three kinds:

#### Individuals

Single values of a given type:

```lean
individual leader : List node           -- mutable (default)
immutable individual maxRound : round   -- immutable/constant
```

#### Relations

Predicates over types:

```lean
relation leader : node -> Bool
relation pending : node -> node -> Bool
relation sent (n : node) : Bool
```

Declare relations as `Bool`-valued (rather than `Prop`-valued): this keeps the
state executable, which is what allows the explicit-state model checker to run
your specification.

#### Functions

Total functions from domain to codomain:

```lean
function currentRound : node -> Nat
immutable function nextNode : node -> node
```

#### Mutability

- **Mutable** (default): Can be modified by actions
- **Immutable**: Part of the background theory, cannot change

```lean
immutable function nextNode : node -> node  -- ring topology is fixed
mutable relation pending : node -> node -> Bool  -- messages can change
```

A constant function or relation can also be a `param` or a type-class field
introduced by `instantiate`. These are parameters of the module rather than
run-time theory values, so the compiled model checker calls them directly and
*might* runs faster; see
[ModelChecker-Guide.md](ModelChecker-Guide.md#constant-functions-and-relations).

### 5. State Generation

After declaring state components, generate the state type:

```lean
#gen_state
```

This assembles all declared state components into a single state structure
that Veil uses for verification.

### 6. Ghost Relations

Ghost relations exist only for specification purposes.
They are defined in terms of other state components:

```lean
ghost relation initial_value (n : address) (r : round) (v : value) :=
  ∀ dst, initial_msg n dst r v

theory ghost relation isMaxRound (r : round) :=
  ∀ r', le r' r
```

- `ghost relation`: Can reference mutable state
- `theory ghost relation`: Only references immutable/background theory

### 7. Initial State

The `after_init` block defines the initial state using an imperative program.
Every Veil model starts in a _default_ state (each field set to its default
value), which the `after_init` program then atomically transitions into the
initial state. The program may be non-deterministic (e.g. use `:= *`
assignments), in which case the model has several initial states:

```lean
after_init {
  leader N := false       -- no initial leader
  pending M N := false    -- no pending messages
}
```

For relation and function state, uppercase variables (like `N`, `M`) are implicitly
universally quantified. The quantified variables are bound on the right-hand
side of the assignment too, so e.g. `W N V := (V == initialValue N)` is
well-formed.

### 8. Actions, Procedures and Transitions

#### Actions

Externally visible transitions that the environment can invoke. Actions are
**atomic**: they execute either fully or not at all (if an assertion fails,
all state changes are discarded).

```lean
action send (n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := true
}

action recv (sender n next : node) {
  require pending sender n
  pending sender n := false
  if sender = n then
    leader n := true
  else
    if le n sender then
      pending sender next := true
}
```

#### Procedures

Internal helper routines that can be called from actions and other procedures,
but cannot be invoked by the environment directly (Veil's `procedure`
corresponds to Ivy's `action`, whereas Veil's `action` corresponds to Ivy's
`export action`):

```lean
procedure sendToNext (payload src : node) {
  let msg := Message.mk payload src (nextNode src)
  if msg ∉ messages then
    messages := msg :: messages
}

action send (n : node) {
  sendToNext n n
}
```

Actions can themselves be called from other actions and procedures.

#### Two-State Transitions

Besides imperative `action`s, transitions can be defined directly as two-state
relations via the `transition` keyword, with the post-state accessed through
primed variables. Any field not mentioned in primed form is implicitly framed
(assumed unchanged):

```lean
transition byz {
  ∀ (src dst : node) (r : round) (v : value),
    (¬ is_byz src ∧ (initial_msg src dst r v ↔ initial_msg' src dst r v)) ∨
    (is_byz src ∧ (initial_msg src dst r v → initial_msg' src dst r v))
}
```

The imperative style is generally preferable — it tends to be more readable and
has significantly better execution performance for model checking — but the
relational style is often more convenient for environment transitions (e.g. a
Byzantine adversary), and the two styles can coexist in the same module. Veil
generates the two-state relation equivalent for every imperative action.

#### Imperative DSL Keywords

| Keyword | Description |
|---------|-------------|
| `require P` | Precondition of the transition (see below) |
| `assume P` | Assumption: executions violating `P` are discarded |
| `assert P` | Must hold (verification condition); aborts the action at runtime if false |
| `let x := e` | Local binding |
| `let x :\| P` | Non-deterministic choice satisfying `P` (Hilbert choice) |
| `let x <- pick T` | Pick arbitrary value of type `T` |
| `x := e` | State update |
| `x ← act` | Call `act` and store its result in `x` (see below) |
| `x := *` | Non-deterministic (unconstrained) state update |
| `if P then ... else ...` | Conditional |
| `return e` | Return value from procedure |

`require P` is the recommended way to express preconditions. When the
enclosing action is invoked by the environment, it behaves as an assumption
(the transition is not enabled unless `P` holds); when the enclosing
action/procedure is called from another procedure, it behaves as an assertion
that the caller must satisfy.

For constrained non-deterministic choice, prefer `let x :| P` over
`pick` + `assume`: it has more efficient execution semantics, as it filters
out invalid values before continuing execution rather than discarding
executions after the fact.

`lhs ← act`, where `lhs` is a state component, a `let mut` local, or an
indexed form of either (`r a ← act`), means `lhs := (← act)`: the call `act` and
its arguments are evaluated on the state *before* the call; then the target's
index terms (e.g., `a` in `r a ← act`) are evaluated and the result is stored on the state *after* the
call. For example, if `bump` increments `k` and returns a value, `r k ← bump`
stores that value at the incremented index.

### 9. Properties

#### Safety Properties

The main correctness properties to verify. As in `after_init`, capitalised
variables are implicitly universally quantified:

```lean
safety [single_leader] leader N ∧ leader M → N = M
```

#### Invariants

Properties that hold in all reachable states (used in inductive proofs;
`safety` is a synonym for `invariant`, used to mark the properties you
actually care about):

```lean
invariant [leader_greatest] leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L
```

#### Assumptions

Axioms about the background theory. Assumptions can refer to `immutable`
state components, `param`s, and type-class fields, but not to `mutable`
components (to assume facts about those, use `trusted invariant`):

```lean
assumption [ring_topology] ∀ n, nextNode (nextNode n) ≠ n
```

Whenever possible, prefer stating assumptions via `instantiate` with a
typeclass from Veil's standard library (e.g. `instantiate tot : TotalOrder
node`): this bundles connected assumptions together, and concrete instances
for execution/model checking are then found automatically by Lean's typeclass
inference.

#### Temporal Properties

Temporal properties are LTL formulas over the runs of the system:

```lean
temporal [electsLeader]
  (∀ n, ∀ next, 𝒲ℱ (send n next)) ∧ (∀ s, ∀ n, ∀ next, 𝒲ℱ (recv s n next)) →
    ◇ ⌜ ∃ l, leader l ⌝

temporal [leaderStays] ∀ l, □ (⌜ leader l ⌝ → ◯ ⌜ leader l ⌝)
```

Formulas use the syntax of [Lentil](https://github.com/verse-lab/Lentil):
state predicates `⌜ P ⌝`, the action atoms `Enabled a`, `⟨ a ⟩`, `𝒲ℱ a` and
`𝒮ℱ a`, the temporal operators `□`, `◇`, `◯`, `𝑈`, `↝` (leads to) and `⇒`,
the usual connectives, and the quantifiers `∀ x, φ` and `∃ x, φ`, which bind
one variable each. The `temporal` docstring explains how Veil reads the atoms,
including partially applied actions such as `𝒲ℱ (send n)`, and the
`(only := check)` and `(only := verify)` options.

### 10. Verification Commands

To enable verification, we need to finalize the module specification:

```lean
#gen_spec
```

Then, we can use a number of verification commands to check the properties of
the module.

To check extraction without exploring the state space, use:

```lean
#gen_executable
```

This generates executable actions and the enumerable transition system used by
`#model_check` and `#simulate`, without running either command. It requires
`#gen_spec` first and can be repeated safely; later model checks reuse the
generated definitions.

#### Checking Invariants

Tries to prove, using SMT solvers, that the conjunction of all `safety` and
`invariant` clauses is an _inductive_ invariant, i.e. holds in all initial
states and is preserved by every action:

```lean
#check_invariants
```

Results are streamed into an InfoView widget. For clauses that are not
preserved, clicking on the clause reveals a _counterexample to induction_
(CTI): a pre-state satisfying the invariant, a transition, and a post-state
violating the clause. Strengthening the invariant with clauses that rule out
such (unreachable) pre-states, guided by CTIs, is the recommended way to
discover an inductive invariant.

If the solver cannot discharge a verification condition, Command + Click on
its name in the widget (or the "Insert" button) inserts the corresponding
proof stub into the editor, where you can prove it interactively using Lean
tactics. The resulting theorem is registered with `@[veil]`, which makes
`#check_invariants` use it to discharge that verification condition.

For induction VCs, inserted stubs use a compact proof command:

```lean
prove_veil_invariant_goal keep inv using wp by
  -- Prove the goal already simplified by `unveil`.
  sorry
```

The arguments select the action (or `initializer`), invariant, and VC style
(`wp` or `tr`). Use `doesNotThrow` in place of the invariant to prove the
exception VC with `using wp`. The command creates and registers the same
`@[veil]` theorem as an explicit signature: `keep_inv` for WP,
`keep_inv_tr` for TR, or `keep_doesNotThrow` for exception freedom.
It requires `#gen_spec`; if `veil.deferVCGeneration` is enabled, it generates
the deferred VCs on demand.

The complete statement is generated from the current specification, and
`unveil` runs before the user tactics. Proof edits reuse Lean's tactic
snapshots, including the initial simplification and unchanged proof prefix.
Existing explicit `@[veil] theorem` declarations remain supported.

To check a single action, use `#check_action <name>`.

#### Synthesizing Invariants

`#updr` tries to prove your `safety` properties automatically. It searches
for extra `invariant` clauses that, together with your `safety` properties
and existing `invariant` clauses, hold in all initial states and are
preserved by every action. If one of your existing invariants is false,
`#updr` reports an execution that violates it.

Run it after `#gen_spec`:

```lean
#updr
```

The command reports one of these results:

- the `invariant` clauses it found.
- an execution that violates a `safety` property.
- that it could not find an invariant, and why.

If it finds clauses, click the suggestion to insert them above `#gen_spec`.
They are then ordinary `invariant` clauses, so `#check_invariants` checks
them as usual. In rare cases, `#check_invariants` rejects a clause that
depends on a state component that `after_init` does not set. The command
warns you when this can happen.

The search runs in the background and shows its progress in the infoview.

If you need a theorem without using `#check_invariants`, run
`#updr certify` followed by `#gen_theorems`. For this option, the other
options, how the search works and its limits, see the
[Invariant Synthesizer Guide](Synthesizer-Guide.md).

#### Explicit-State Model Checking

Exhaustive enumeration of the reachable states of a finite instance, checking
every `safety` and `invariant` clause in each state. The first argument
instantiates the module's parameters (`type`s and `param`s); the second gives
concrete values for the theory (`immutable`) components and can be omitted
when there are none:

```lean
#model_check { node := Fin 4 }
```

```lean
#model_check { node := Fin 4 } { nextNode := fun n => n + 1 }
```

Typeclass assumptions introduced via `instantiate` are resolved using Lean's
typeclass inference for the concrete instantiation (the model checker does
_not_ enumerate all possible instances or theories, so treat it as a testing
tool). Progress and action-coverage statistics are displayed live in an
InfoView widget; if a violation is found, Veil shows a concrete counterexample
trace. See the [Model Checker Guide](ModelChecker-Guide.md) for execution modes,
options, deadlocks, state constraints, and performance tuning.

##### Random Simulation

If you do not want exhaustive testing, you can use the `#simulate` command to
perform random walks on the state graph. Provide the type instantiation and
theory, optionally followed by the settings:

```lean
#simulate { node := Fin 3 } {} (numTraces := 2000) (maxSteps := 500) (seed := 42)
```

#### Symbolic Bounded Model Checking

Explore system behaviors with trace queries, discharged via SMT. Unlike
`#model_check`, these queries check **all** instantiations of the module's
parameters at once, but only up to a bounded number of steps:

##### Satisfiable Traces

Find an execution reaching a state:

```lean
sat trace {
  any 3 actions
  assert (∃ l, leader l)
}
```

You can also specify concrete actions to take, and optionally name the trace:

```lean
sat trace [some_progress] {
  send
  send
  recv
}
```

A query worth including in any specification is `sat trace { }` (the empty
trace): it checks that the module's assumptions are satisfiable, guarding
against vacuously-verified specifications.

##### Unsatisfiable Traces

Prove no execution of the given (bounded) shape reaches a state:

```lean
unsat trace {
  any 5 actions
  assert (∃ n₁ n₂, n₁ ≠ n₂ ∧ leader n₁ ∧ leader n₂)
}
```

Note that checking time grows exponentially with the trace length.

#### Checking Temporal Properties

`#temporal_check` model checks the module's temporal properties on a finite
instance, with the same arguments as `#model_check`:

```lean
#temporal_check { node := Fin 3 }
#temporal_check [electsLeader] { node := Fin 3 }
```

It explores every infinite run of the instance, including runs that never take
an enabled action, so liveness properties usually need fairness assumptions, as
in `electsLeader`. See the [Temporal Checker Guide](TemporalChecker-Guide.md).

#### Proving Temporal Properties

`prove_temporal_by` proves a temporal property for all instantiations of the
module, in the proof mode of [Lentil](https://github.com/verse-lab/Lentil):

```lean
prove_temporal_by [leaderStays]
  tclear hInit hInv   -- neither the initial state nor the invariants are needed
  tintro l
  tmonotone           -- reduce `□ (…)` to a single step
  unveil_temporal     -- turn the goal into a first-order goal about the fields
  grind
```

The resulting theorem is `leaderStays._proof`. It assumes the invariants
(`hInv`) rather than proving them; prove them with `#check_invariants`. Besides
Lentil's tactics and proof rules (e.g. WF1), Veil provides `unveil_temporal`
and `veil_solve_temporal`. See
[Examples/Liveness/TLA/Consensus.lean](../Examples/Liveness/TLA/Consensus.lean)
for a liveness proof.

Unlike `#temporal_check`, which repeats a state without successors forever,
proofs only consider runs in which every step is an action. If the system can
stop, add an action that does nothing (as `stutter` in `Consensus.lean`).
