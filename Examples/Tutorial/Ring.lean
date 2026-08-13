import Veil

-- This makes the Veil DSL available in this file, and imports the Veil
-- standard library (`Veil.Std`), which contains a number of useful
-- first-order-logic axiomatisations of common structures.

/-! # Leader Election in a Ring

This file specifies a very simple distributed protocol in Veil, showcasing the
framework's main features.

The protocol is leader election in a ring. It works as follows:

- There are a finite number of nodes, each of which has a unique identifier.
- The nodes are arranged in a ring topology, where each node has a unique
  successor and predecessor. Nodes can only send messages to their immediate
  successor. (That is, the ring is unidirectional.)
- The goal is for one node to be elected as leader.
- Every node sends a message containing its identifier to its successor.
- When a node receives a message, it only forwards it along the ring if the
  contained identifier is GREATER than its own.
- A node becomes the leader if it receives its own identifier from its
  predecessor.

The protocol works because only the node with the highest identifier can
circulate its message around the entire ring. Each node forwards messages
containing higher identifiers than its own. Since identifiers are unique, the
maximum identifier will eventually return to its originating node, which becomes
the leader. All other identifiers get blocked by nodes with higher identifiers
during their traversal.

Concretely, the protocol has the following _safety_ property: at most one node
can be elected as leader.

In the remainder of this file, we will specify the protocol in Veil, test it
using Veil's explicit-state model checker, and prove its correctness
automatically using SMT.
-/

/- This defines a new Veil module named `Ring`. In Lean terms, `Ring` is a
`namespace` in which Veil's module DSL is available. -/
veil module Ring

/- This defines a new (uninterpreted) type `node`, to represent node IDs. The
`type` command in Veil defines a type parameter of the module, together with
`DecidableEq` and `Nonempty`/`Inhabited` instances, which make it sound to use
as an SMT sort and possible to execute. When verifying, Veil universally
quantifies over `node`, i.e. it proves the protocol correct for _all_ types
`node`; when model checking, we provide a concrete instantiation (e.g.
`Fin 4`). -/
type node

/- This instantiates the `TotalOrder` class for `node`. You can right-click and
'Go to definition' (F12) to see the axioms this introduces.

Concretely, it defines an (immutable) relation `tot.le` between nodes, and
provides the standard reflexivity, transitivity, antisymmetry, and totality
axioms for it. -/
instantiate tot : TotalOrder node

/- This instantiates the `Between` class for `node`. It encodes the fact that
the `node`s form a (unidirectional) ring topology.

It defines an (immutable) relation `btwn.btw (x y z : node)` between nodes, read
as "y is between x and z".

An illustration of a ring, going clockwise:

    .---.---.
   /         \
  w           x      in this illustration, the ring goes clockwise
  |           |      (i.e. w -> x -> y -> z -> w)
  z           .
   \         /
    .---.---y

The relation `btw x y z` means that `y` lies between `x` and `z`, as
shown in the diagram above.

The axioms are as follows:
- [btw_ring] `∀ x y z, btw x y z → btw y z x`
- [btw_trans] `∀ w x y z, btw w x y → btw w y z → btw w x z`
- [btw_side] `∀ w x y, btw w x y → ¬ btw w y x`
  - this encodes the fact that the ring is unidirectional: in our
  example diagram, it is NOT the case that `y` is between `w` and `x`,
  since that would entail going counter-clockwise, which is not allowed
  (since, for illustration, we chose the ring to go clockwise)
- [btw_total] `∀ w x y, btw w x y ∨ btw w y x ∨ w = x ∨ w = y ∨ x = y`
-/
instantiate btwn : Between node

/- We open the `Between` and `TotalOrder` namespaces, so that we can use the
`le` and `btw` relations without prefixing them with `tot` and `btwn`. -/
open Between TotalOrder

/-
We model the state of this protocol as follows, with two relations:

- `leader : node → Bool` tracks which nodes believe they are the leader;
  `leader n = true` means node `n` believes it is the leader.

   The safety property is that at most one node can be elected as leader, i.e.
   `∀ n1 n2, leader n1 ∧ leader n2 → n1 = n2`. We will specify this later.

- `pending : node → node → Bool` tracks messages in transit, where
  `pending id dst` means there is a message containing node `id`'s ID that has
  been sent to node `dst`. Note that, for simplicity, we do not model the
  immediate sender of the message, but only its _original_ sender (which
  matches the ID within the message). There is no need to track the full path
  a message has taken through the ring.

  NOTE: we declare relations as `Bool`-valued (rather than `Prop`-valued).
  This keeps the state executable, which is what lets Veil's explicit-state
  model checker run the specification.
-/
relation leader : node → Bool

-- `pending id dst = true` means there is a message containing node `id`'s ID
-- that has been sent to (and can be received by) node `dst`.
-- (This shows the alternative syntax with named arguments.)
relation pending (id : node) (dst : node) : Bool

/- This assembles the previously declared components into the state type of the
`Ring` transition system. Conceptually, the generated `State` corresponds to
the following `structure` definition:

```lean
structure State where
  leader : node → Bool
  pending : node → node → Bool
```

(The actual generated type is parametric in the concrete runtime
representation of each field, which lets the model checker use efficient data
structures; you can inspect it with `#print State`.) -/
#gen_state

/- Veil's model of a specification is a state transition system. Having just
defined the type of states, we now define the initial state.

Every Veil model starts in a _default_ state (with every field set to its
default value), which is then immediately, atomically modified by the
(possibly non-deterministic) imperative program specified in the `after_init`
block. In practice, you can think of `after_init` as directly specifying the
initial state(s). -/
after_init {
  /- In assignments (and `safety` / `invariant` clause declarations), capital
  letters are implicitly universally quantified. This is a convention we adopt
  from Ivy. For instance, `leader N := false` means that for all nodes `n`,
  `leader n = false`. -/
  leader N := false
  /- i.e. `∀ m n, pending m n := false`,
    or equivalently: `pending := fun M N => false` -/
  pending M N := false
}

/-
_Actions_ in Veil are imperative code fragments that modify the state. For
verification purposes, Veil "compiles" actions to two-state transition
relations (i.e. predicates over a pre-state and a post-state); for execution
(testing), it uses their imperative semantics directly.

Here we define an action `send`, with parameters `n` and `next` of type `node`,
that specifies what node `n` does when it initiates the protocol, i.e. it sends
a message containing its own ID to its successor (`next`).
-/
action send (n next : node) {
  /- A `require` statement specifies a precondition that must be satisfied for
  the action to take effect / trigger. Here we encode that `next` is indeed
  the successor of `n` in the ring. -/
  require n ≠ next ∧ ∀ Z, ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := true
}

/- Instead of "inlining" the condition for a node `next` to be the successor of
`n` in all our actions, we can define a `ghost` `relation`, i.e. a derived
definition given in terms of the "real" state and theory. (In this case,
`isNext` does not in fact depend on the mutable state, but it could.) -/
ghost relation isNext (n next : node) :=
  (n ≠ next) ∧ (∀ N', (N' ≠ n ∧ N' ≠ next) → ¬ btw n N' next)

/- `n` receives a message containing `sender`'s ID, and potentially forwards
it to `next`. -/
action recv (sender n next : node) {
  require isNext n next
  require pending sender n
  /- We use non-deterministic assignment to model that the message may or may
  not be removed (i.e. it can potentially be received many times). -/
  pending sender n := *

  /- This is equivalent to the following Veil code:
  ```lean
  let isPresent ← pick Bool
  pending sender n := isPresent
  ```

  Non-deterministic assignment is more general and also lets us express things
  like `pending ID N := *` (the entirety of the `pending` relation becomes
  indeterminate). To obtain a non-deterministic value _constrained_ by a
  predicate, use the Hilbert-choice binding form `let x :| P`.
  -/

  /- Veil `action`s are in fact an extended form of `do` notation, so you can
  use standard Lean syntax and `do`-notation features like `let mut` in them. -/
  if (sender = n) then
    leader n := true
  else
    if (le n sender) then
      pending sender next := true
}

/- This is the safety property we want to establish. `L1` and `L2` are
implicitly universally quantified, i.e. this means:
`∀ (L1 L2 : node), leader L1 ∧ leader L2 → L1 = L2` -/
safety [single_leader] leader L1 ∧ leader L2 → L1 = L2

/- These invariant clauses together with the safety property above form an
inductive invariant. COMMENT THEM OUT to see how Veil can be used to manually
discover invariants, guided by counterexamples to induction. -/

invariant [leader_greatest] leader L → le N L
invariant [receive_self_msg_only_if_greatest] pending L L → le N L
invariant [no_bypass] pending S D ∧ btw S N D → le N S

/- Before we can operate on the specification in any way (e.g. check it), we
must run the `#gen_spec` command. -/
#gen_spec

/-! ## Testing the specification

Before attempting a proof, it is a good idea to _check_ two things: that the
model satisfies the desired safety properties, and that it does so for
substantive reasons—not simply because the model is vacuous (i.e. admits no
interesting executions). Veil has two complementary testing techniques for
this: _concrete_ (explicit-state) model checking of finite instances, and
_symbolic_ bounded model checking of unbounded instances.
-/

/- The `#model_check` command below runs Veil's explicit-state model checker
directly from the editor buffer. It takes two arguments:

1. The _instantiation_: a concrete assignment for the module's parameters
   (everything declared with `type` or `param`). Here we say `node := Fin 4`,
   i.e. we check an instance of the protocol with exactly 4 nodes. Typeclass
   assumptions introduced via `instantiate` (here, `TotalOrder` and `Between`)
   are resolved automatically using Lean's typeclass inference for the
   concrete type.

2. The _theory_: concrete values for all `immutable` state components. The
   `Ring` module has none, so we pass the empty structure `{ }`.

The model checker exhaustively enumerates all states reachable from the
initial state(s) via breadth-first search, checking every `safety` and
`invariant` clause in each state. Placing your cursor on the command shows an
interactive panel in the InfoView, with live statistics and an _action
coverage_ table showing how often each action was executed. If every action
executes successfully at least once, the model is not vacuous. If a violation
is found, Veil displays a concrete counterexample trace leading to the bad
state.

NOTE: the model checker checks only the specific instantiation and theory you
provide (with the default typeclass instances), so it is a _testing_ tool: it
does not prove the protocol correct for all instances. That is what
`#check_invariants` (below) is for. -/
#model_check { node := Fin 4 } { }

/- Veil also supports _symbolic_ bounded model checking via SMT, using trace
specifications. We use these especially to validate that our protocol
specifications are non-vacuous, i.e. they do actually admit interesting
executions—but unlike `#model_check`, these queries reason about _all_
instantiations of the parameters at once.

A trace specification consists of:
- `sat`/`unsat` — is the trace satisfiable (an execution of this shape
  exists), or unsatisfiable (no such execution exists)?
- `[an_optional_name]` — the name of the trace; can be omitted
- `{ ... }` — the trace specification, consisting of:
  - a sequence of actions, either explicitly listed by name or using
    `any action` or `any N actions`
  - `assert` statements to be checked against the state at that point in the
    trace

For `sat` traces, Veil reports the discovered execution (including the
discovered instantiation) in the InfoView; for `unsat` traces, it reports
whether a counterexample exists. -/

/- This checks that there exists an initial state, i.e. that the module's
assumptions are satisfiable. (It is possible to write inconsistent
assumptions, and this query guards against that.) -/
sat trace [initial_state] { }

/- Three specific steps suffice to elect a leader (when there are enough
nodes). -/
sat trace [can_elect_leader_explicit] {
  send
  recv
  recv
  assert (∃ l, leader l)
}

/- The same, but letting the solver choose which actions to take. -/
sat trace [can_elect_leader] {
  any 3 actions
  assert (∃ l, leader l)
}

/- No execution of `send` can leave the network empty. -/
unsat trace {
  send
  assert (¬ ∃ n next, pending n next)
}

/- Bounded verification: within 6 arbitrary actions, it is impossible to
violate the `leader_greatest` invariant—for any number of nodes. -/
unsat trace [trace_any] {
  any 6 actions
  assert ¬ (leader L → le N L)
}

/-! ## Verifying the specification

Having tested the protocol, we now _prove_ it safe for all instances and
executions of unbounded length.
-/

/- The `#check_invariants` command tries to prove, using SMT solvers, that the
conjunction of all `safety` and `invariant` clauses is an _inductive_
invariant, i.e. that it (a) holds in all initial states, and (b) is preserved
by every action. Since the conjunction includes `single_leader`, this
establishes that the protocol is safe.

TIP: hover over the command (or place your cursor on it) to see the results
in the InfoView, streamed in as the checks complete.

If you COMMENT OUT the `invariant` clauses above, you will see output like:

Initialization must establish the invariant:
  doesNotThrow ... ✅
  single_leader ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  send
    doesNotThrow ... ✅
    single_leader ... ✅
  recv
    doesNotThrow ... ✅
    single_leader ... ❌

(The `doesNotThrow` property is not part of the invariant; it is a check that,
assuming the invariant, the action satisfies all its `assert` statements, i.e.
"does not throw" an exception.)

Clicking on a failed clause reveals a _counterexample to induction_ (CTI): a
pre-state `st` that satisfies the candidate invariant, and a post-state `st'`
reached from `st` by the failing action (here `recv`), with `st'` violating
the given clause. For example, you might see a two-node instance where the
node with the *smaller* ID is marked as leader in the pre-state.

Such a pre-state is not in fact reachable in valid executions of the protocol:
a node can only become leader if it has the highest ID. But nothing in our
candidate invariant rules it out—that is exactly what the CTI is telling us.
To eliminate this CTI, we add the following clause to our invariant:

```lean
invariant [leader_greatest] leader L → le N L
```

We repeat this process—run `#check_invariants`, inspect the CTI, add a
clause—until all CTIs are eliminated and the invariant becomes inductive.
This is the Ivy-style counterexample-driven invariant discovery workflow.

TIP: while iterating, keep the `#model_check` command above in the file: if
you add a candidate clause that is _not_ actually an invariant (i.e. it
excludes a reachable state), the model checker will flag it, saving you from
chasing CTIs for an unprovable invariant.

TIP: if the SMT solver cannot prove a verification condition, you can
Command+Click on its name in the InfoView widget (or press the "Insert"
button) to insert the corresponding theorem statement into the editor buffer,
and prove it interactively using Lean tactics. The inserted theorem is tagged
with the `@[veil]` attribute, which makes `#check_invariants` pick it up and
use it to discharge the corresponding verification condition. -/
#check_invariants

end Ring
