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
9. Properties (safety, invariants, assumptions)
10. Specification generation & verification commands

### 1. Module Declaration

A Veil module begins with `veil module <Name>` and ends with `end <Name>`:

```lean
import Veil

veil module Ring
-- module contents go here
end Ring
```

The `import Veil` statement brings in all Veil DSL syntax and utilities.

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

Axioms about the background theory. Assumptions can only refer to `immutable`
state components (to assume facts about `mutable` components, use
`trusted invariant`):

```lean
assumption [ring_topology] ∀ n, nextNode (nextNode n) ≠ n
```

Whenever possible, prefer stating assumptions via `instantiate` with a
typeclass from Veil's standard library (e.g. `instantiate tot : TotalOrder
node`): this bundles connected assumptions together, and concrete instances
for execution/model checking are then found automatically by Lean's typeclass
inference.

### 10. Verification Commands

To enable verification, we need to finalize the module specification:

```lean
#gen_spec
```

Then, we can use a number of verification commands to check the properties of
the module.

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
theorem statement into the editor, where you can prove it interactively using
Lean tactics. The inserted theorem is tagged `@[veil]`, which makes
`#check_invariants` use it to discharge that verification condition.

To check a single action, use `#check_action <name>`.

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
trace.

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
