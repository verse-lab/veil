import Veil
-- This makes the Veil DSL available in this file, and imports
-- the Veil standard library (`Veil.Std`), which contains a number of
-- useful first-order-logic axiomatisations of common structures.

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

In the remainder of this file, we will specify the protocol in Veil, and prove
its correctness automatically using SMT.
-/

/- This defines a new Veil module named `Ring`. In Lean terms, `Ring` is a
`namespace` in which we have executed `open Classical`. -/
veil module Ring

/- This defines a new (uninterpreted) type `node`, to represent node IDs. The
`type` command in Veil defines a Lean type that is sound to use as an SMT sort,
i.e. one that comes with an instance of the `Nonempty` typeclass. -/
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

    .---.---.
   /         \
  w           z
  |           |      ring goes counter-clockwise (i.e. w -> x -> y -> z -> w)
  x           .
   \         /
    .---.---y

The relation `btw x y z` means that `y` lies between `x` and `z` when traversing
the ring counter-clockwise, as shown in the diagram above.

The axioms are as follows:
- [btw_ring] `∀ x y z, btw x y z → btw y z x`
- [btw_trans] `∀ w x y z, btw w x y → btw w y z → btw w x z`
- [btw_side] `∀ w x y, btw w x y → ¬ btw w y x`
  - this encodes the fact that the ring is unidirectional: it is NOT the case
    that `y` is between `w` and `x` since that would entail going
    clockwise, which is not allowed
- [btw_total] `∀ w x y, btw w x y ∨ btw w y x ∨ w = x ∨ w = y ∨ x = y`
-/
instantiate btwn : Between node

/- We open the `Between` and `TotalOrder` namespaces, so that we can use the
`le` and `btw` relations without prefixing them with `tot` and `btwn`. -/
open Between TotalOrder

/-
We model the state of this protocol as follows, with two (FOL) relations:
- `leader : node → Prop` tracks which nodes believe they are the leader
  `leader n = True` means node `n` believes it is the leader.

   The safety property is that at most one node can be elected as leader, i.e.
   `∀ n1 n2, leader n1 ∧ leader n2 → n1 = n2`. We will specify this later.

- `pending : node → node → Prop` tracks messages in transit, where `pending s d`
  means there is a message containing node `s`'s ID that has been sent to node
  `d`. Note that, for simplicity, we do not model the sender of the message
  (e.g. by defining the relation as
  `pending (src : node) (id : node) (dest : node)`), but only its _original_
  sender (which matches the ID within the message). There is no need to track
  the full path a message has taken through the ring.
-/

/- `leader n = True` means node `n` believes it is the leader.

  NOTE: make sure you use `Prop` (`True` / `False`) in Veil rather than `bool`
  (`true` / `false`). You might see very confusing error messages if you use the
  latter. We are working on making this more user-friendly. -/
relation leader : node → Prop
-- alternative syntax: `relation leader (n : node)`

-- `pending id dest = True` means there is a message containing node `id`'s ID
-- that has been sent to (and can be received by) node `dest`
relation pending (id : node) (dest : node)


/- This declares an inductive datatype `Ring.State` that encodes the state of
the Ring transition system / protocol. -/
#gen_state

/- We can inspect the generated datatype. This is a regular Lean definition
(rather than a deeply-embedded object), so you can use it in any context you
want within Lean. It corresponds to the following `structure` definition:

```lean
structure State (node : Type) where
  leader : node -> Prop
  pending : node -> node -> Prop
deriving Nonempty
```

Note that this type is parametric in the `node` type, which is a parameter (Lean
`variable`) of the `Ring` module / namespace. -/
#print State

/- Veil's model of a specification is a state transition system. Having just
defined the type of states, we now define the initial state.

Formally, every Veil transition system has an indeterminate (nondeterministic)
_initial state_, which is immediately modified by an _action_ specified in the
`after_init` block.

In practice, you can think of `after_init` as directly specifying the initial
state, however. Indeed, in Veil, it defines the `initialState?` property, which
is a definition of type `State → Prop`.
-/
after_init {
  /- In assignments (and `safety` property and `invariant` clause declarations),
  capital letters are universally quantified. This a convention we adopt from
  Ivy. For instance, `leader N := False` means that for all nodes `n`,
  `leader n = False`. -/
  leader N := False
  /- `∀ m n, pending m n := False`
    or equivalently: `pending := fun M N => False` -/
  pending M N := False
}

#print initialState?
-- `fun st' => st' = { leader := fun N => False, pending := fun M N => False }`

/-
_Actions_ in Veil are imperative code fragments that modify the state. Veil
"compiles" actions to two-state transition relations (i.e. definitions of type
`State → State → Prop`).

Here we define an action `send`, with parameters `n` and `next` of type `node`,
that specifies what node `n` does when it initiates the protocol, i.e. it sends
a message containing its own ID to its successor (`next`).
-/
action send (n next : node) = {
  /- A `require` statement specifies a condition that must be satisfied for the
  action to take effect / trigger. Here we encode that `next` is indeed the
  successor of `n` in the ring. -/
  require n ≠ next ∧ ∀ Z, ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := True
}

/- The `action` specification above produces a number of Lean definitions,
including `send.tr`, which is the transition relation for the `send` action. -/
#print send.tr

/- Instead of "inlining" the condition for a node `next` to be the successor of
`n` in all our actions, we can define a `ghost` `relation`, i.e. a derived
relation defined in terms of the "real" state. (In this case, `isNext` does not
in fact depend on the state, but it could.) -/
ghost relation isNext (n next : node) :=
  (n ≠ next) ∧ (∀ N', (N' ≠ n ∧ N' ≠ next) → ¬ btw n N' next)

#print isNext

/- `n` receives a message containing `id`, and potentially forwards it to `next`. -/
action recv (id n next : node) = {
  require isNext n next
  require pending id n
  /- We use non-deterministic assignment to model that the message may or may
  not be removed (i.e. it can potentially be received many times). -/
  pending id n := *

  /- This is equivalent to the following Veil code:
  ```lean
  let isPresent ← fresh
  pending id n := isPresent
  ```

  Non-deterministic assignment is more general also lets us express things like
  `pending ID N := *` (the entirety of the `pending` relation is now
  indeterminate), i.e.:
  ```lean
  let newPending ← fresh
  pending := newPending
  ```
  -/

  /- Veil `action`s are in fact an extended form of `do` notation, so you can
  use standard Lean syntax and `do`-notation features like `let mut` in them -/
  if (id = n) then
    leader n := True
  else
    if (le n id) then
      pending id next := True
}

#print recv.tr

/- This is the safety property we want to establish. `L1` and `L2` are
implicitly universally quantified, i.e. this means:
`∀ (L1 L2 : node), leader L1 ∧ leader L2 → L1 = L2` -/
safety [single_leader] leader L1 ∧ leader L2 → L1 = L2
#print single_leader

/- These invariant clauses together with the safety property above form an
inductive invariant. COMMENT THEM OUT to see how Veil can be used to manually
discover invariants, guided by counterexamples to induction. -/

invariant [leader_greatest] leader L → le N L
invariant [receive_self_msg_only_if_greatest] pending L L → le N L
invariant [no_bypass] pending S D ∧ btw S N D → le N S

/- Before we can operate on the specification in any way (e.g. check it), we
must run the `#gen_spec` command. -/
#gen_spec

set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true

/- The `transition` VC style gives more readable counter-examples, since
those show both the pre-state and post-state. -/
set_option veil.vc_gen "transition"

/- TIP: Press the pause (⏸) button in the Lean Infoview to "lock" the
counter-example, so you can look at it while you type the `invariant` clause you
want to add above. Then press play (▶) button to re-check the spec with the
newly added invariant. -/
#check_invariants

/-

If you COMMENT OUT the `invariant` clauses above, you will see the following
output. This shows that the `single_leader` invariant is not preserved by the
`recv` action, i.e.

Initialization must establish the invariant:
  single_leader ... ✅
The following set of actions must preserve the invariant:
  send
    single_leader ... ✅
  recv
    single_leader ... ❌

Counter-examples
================

recv_single_leader:
interpreted sort Bool
sort node = #[node0, node1]
n = node0
next = node1
sender = node0
st.leader(node1) = true
st.pending(node0, node0) = true
st'.leader(node0) = true
st'.leader(node1) = true
tot.le(node0, node0) = true
tot.le(node1, node0) = true
tot.le(node1, node1) = true

This is a counterexample to induction (CTI). It shows a pre-state (`st`) that
satisfies the inductive invariant, and a post-state (`st'`) which is reached
from `st` by the `recv` action, but with `st'` not satisfying the
`single_leader` property.

The pre-state `st` is not in fact reachable in valid executions of the protocol,
since here `node` is a leader, but it is not the node with the highest ID
(`tot.le(node1, node0`, i.e. `node1 ≤ node0`). This cannot be the case. To
eliminate this CTI, we add the following clause to our invariant:

```lean
invariant [leader_greatest] leader L → le N L
```

We can repeat this process until we eliminate all CTIs and thus find an
inductive invariant that establishes the safety of the system.
-/

/- TIP: you can run `#check_invariants!` to see the theorem statements that
couldn't be proven. In this case: -/
-- #check_invariants!
@[invProof]
  theorem recv_single_leader_ :
      ∀ (st st' : @State node),
        (@System node node_dec node_ne tot btwn).assumptions st →
          (@System node node_dec node_ne tot btwn).inv st →
            (@Ring.recv.tr node node_dec node_ne tot btwn) st st' →
              (@Ring.single_leader node node_dec node_ne tot btwn) st' :=
    by (unhygienic intros); solve_clause[Ring.recv.tr] Ring.single_leader

/- TIP: `#check_invariants?` will print all theorems that will be checked. -/
-- #check_invariants?

/- Veil also provides facilities for interactively proving the safety of state
transition systems, as shown below: -/

prove_inv_init by { simp_all [initSimp, actSimp, invSimp] }

prove_inv_safe by {
  sdestruct st;
  simp [invSimp]
}

/- We support proof reconstruction from SMT proofs (powered by `lean-smt`). This
is not yet fully reliable, but it suffices for this simple example. Note that
`prove_inv_inductive` shows no warning about `sorry` with the option enabled. -/
set_option veil.smt.reconstructProofs true

prove_inv_inductive by {
  constructor
  . apply inv_init
  intro st st' has hinv hnext
  sts_induction <;> sdestruct_goal <;> solve_clause
}

/- We also support bounded model checking to validate the protocol. We use this
especially to validate that our protocol specifications are non-vacuous, i.e.
they do actually admit interesting executions. -/

/- This checks that there exists an initial state. -/
sat trace [initial_state] {} by { bmc_sat }

/- A trace specification consists of:
- `sat`/`unsat` -- is the trace satisfiable?
- `[an_optional_name]` -- the name of the trace; can be omitted
- `{ ... }` -- the trace specification, consisting of:
  - a sequence of actions, either explicitly listed or using `any action` or
    `any N actions`
  - `assert` statements to be checked against the state at that point in the
    trace
- `by bmc_sat / bmc ` -- the proof

TIP: you can put your cursor after `by` to see the Lean proof obligation that is
automatically discharged.
-/
sat trace [three_nodes_can_elect_leader] {
  assert (∃ (n1 n2 n3 : node), n1 ≠ n2 ∧ n1 ≠ n3 ∧ n2 ≠ n3)
  send
  recv
  recv
  recv
  assert (∃ n, leader n)
} by { bmc_sat }

sat trace {
  send
  assert (∃ n next, pending n next)
} by { bmc_sat }


sat trace [can_elect_leader_explicit] {
  send
  assert (∃ n next, pending n next)
  recv
  recv
  assert (∃ l, leader l)
} by { bmc_sat }

sat trace [can_elect_leader] {
  any 3 actions
  assert (∃ l, leader l)
} by { bmc_sat }

unsat trace {
  send
  assert (¬ ∃ n next, pending n next)
} by { bmc }

sat trace {
  send
  assert (∃ n next, pending n next)
} by { bmc_sat }

unsat trace [trace_any] {
  any 6 actions
  assert ¬ (leader L → le N L)
} by { bmc }

end Ring
