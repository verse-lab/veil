# Veil: A Framework for Automated and Interactive Verification of Transition Systems

[![Actions status](https://github.com/verse-lab/veil/actions/workflows/ci.yml/badge.svg)](https://github.com/verse-lab/veil/actions)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)


Veil is a _foundational_ framework for (1) specifying, (2)
implementing, (3) testing, and (4) proving safety (and, in the future,
liveness) properties of state transition systems, with a focus on
distributed protocols.

Veil is embedded in the [Lean 4 proof assistant](https://lean-lang.org/) and provides push-button
verification for transition systems and their properties expressed
decidable fragments of first-order logic, with the full power of a
modern higher-order proof assistant for when automation falls short.

## Veil 2.0 Pre-Release

You are looking at a **pre-release version** of Veil 2.0, the upcoming major
version of Veil. There are still quite a few bugs and rough edges.

If you encounter issues, please [report them to
us](https://github.com/verse-lab/veil/issues/new), so we can fix them before
the release. Your patience and feedback are greatly appreciated!

## Online Playground

We provide a live environment to try out Veil 2.0, at the following URL:

<p align="center"><a href="https://try.veil.dev"><big><b>try.veil.dev</b></big></a></p>

## Tutorial

We will be looking at two files in the tutorial, both of which encode the Ring Leader Election protocol, but in different styles:

- [Examples/Tutorial/RingFin.lean](Examples/Tutorial/RingFin.lean)
- [Examples/Tutorial/RingDec.lean](Examples/Tutorial/RingDec.lean)

These files are also available in the [online playground](#online-playground), under the Examples button, as "Ring (Concrete)" and "Ring (Decidable)", respectively.

## Build

Veil requires [Lean 4](https://github.com/leanprover/lean4) and
[NodeJS](https://nodejs.org/en/download/). To install those on Linux or MacOS:

```bash
# Install Lean
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable

# Install NodeJS
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.40.3/install.sh | bash
\. "$HOME/.nvm/nvm.sh"
nvm install 24
```

Then, clone Veil:

```bash
git clone https://github.com/verse-lab/veil.git
cd veil && git checkout veil-2.0
```

And, finally, build it:

```bash
lake exe cache get
lake build
```

The `lake exe cache get` command downloads a pre-built version of
[mathlib](https://github.com/leanprover-community/mathlib4), which otherwise
would take a very long time to build.

### Troubleshooting

**(NPM errors)** If you see an error about `npm`, make sure it's in your
`PATH`; the command above installs both `node` and `npm`.

**(cvc5 errors)** If you see an error about `cvc5`, run:

```bash
rm -rf .lake/packages/cvc5
lake build
```

There is a sporadic issue in the build process for
[`lean-cvc5`](https://github.com/abdoo8080/lean-cvc5). Trying to build again
often fixes the problem.

## Veil DSL Highlights

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
8. Procedures and actions
    - procedures are internal helper routines that can be called from actions
    - actions are externally visible transitions that the environment can invoke
9. Properties (safety, invariants, assumptions)
10. Specification generation & verification commands

We'll use the **Ring Leader Election** protocol as our running example.

### 1. Module Declaration

A Veil module begins with `veil module <Name>` and ends with `end <Name>`:

```lean
import Veil

veil module RingDec
-- module contents go here
end RingDec
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

Predicates over types (return `Bool` or are propositional):

```lean
relation leader : node -> Bool
relation pending : node -> node -> Bool
relation sent (n : node) : Bool
```

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

The `after_init` block defines the initial state using an imperative program:

```lean
after_init {
  leader N := false       -- no initial leader
  pending M N := false    -- no pending messages
}
```

For relation and function state, uppercase variables (like `N`, `M`) are implicitly
universally quantified.

### 8. Actions and Procedures

#### Actions

Externally visible transitions that the environment can invoke:

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

Internal helper routines that can be called from actions:

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

#### Imperative DSL Keywords

| Keyword | Description |
|---------|-------------|
| `require P` | Precondition (filters valid executions) |
| `assume P` | Assumption for this execution path |
| `assert P` | Must hold (verification condition) |
| `let x := e` | Local binding |
| `let x :\| P` | Non-deterministic choice satisfying `P` |
| `let x <- pick T` | Pick arbitrary value of type `T` |
| `x := e` | State update |
| `if P then ... else ...` | Conditional |
| `return e` | Return value from procedure |

### 9. Properties

#### Safety Properties

The main correctness properties to verify:

```lean
safety [single_leader] leader N ∧ leader M → N = M
```

#### Invariants

Properties that hold in all reachable states (used in inductive proofs):

```lean
invariant [leader_greatest] leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L
```

#### Assumptions

Axioms about the background theory (immutable state):

```lean
assumption [ring_topology] ∀ n, nextNode (nextNode n) ≠ n
assumption [total_order] ∀ a b, le a b ∨ le b a
```

### 10. Verification Commands

To enable verification, we need to finalize the module specification:

```lean
#gen_spec
```

Then, we can use a number of verification commands to check the properties of
the module.

#### Checking Invariants

Verifies all invariants using SMT solvers:

```lean
#check_invariants
```

Command + Click on any theorem name in the widget will insert the theorem
statement into the editor.

#### Explicit State Model Checking

Bounded exhaustive checking with concrete types:

```lean
#model_check { node := Fin 4 }
```

For modules with theory components, you need to provide the concrete values for
the theory components:

```lean
#model_check { node := Fin 4 }
{ nextNode := fun n => n + 1,
  le := fun n m => n < m }
```

#### Symbolic Model Checking

Explore system behaviors with trace queries:

##### Satisfiable Traces

Find an execution reaching a state:

```lean
sat trace {
  any 3 actions
  assert (∃ l, leader l)
}
```

You can also specify concrete actions to take, e.g.:

```lean
sat trace {
  send
  send
  recv
}
```

##### Unsatisfiable Traces

Prove no execution reaches a state:

```lean
unsat trace {
  any 5 actions
  assert (∃ n₁ n₂, n₁ ≠ n₂ ∧ leader n₁ ∧ leader n₂)
}
```
