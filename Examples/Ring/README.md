# Ring leader election by CSLib simulation

This ports the ring refinement example from `george-phd-thesis` to CSLib's
`LTS.IsSimulation`.

- `RingAbs.lean` defines the abstract protocol with relational leader and pending
  state. `#gen_theorems` proves `RingAbs.single_leader.is_inv`, using reconstructed
  SMT proofs (`veil.smt.trust false`).
- `RingConc.lean` defines the concrete protocol with natural-number identifiers,
  a list of leaders, and a list of messages. The node list is duplicate-free and
  has at least two members. Its order specifies the ring, independently of the
  ordering of identifiers used to compare candidates.
- `RingRef.lean` proves `RingRef.sim` using CSLib and transfers the abstract
  invariant to `RingRef.single_leader_safety`: every reachable concrete state
  has at most one leader.

For each fixed concrete theory, the abstract node type is the subtype of members
of `allNodes`. The refinement relation connects list membership to the abstract
Boolean relations and maintains the concrete well-formedness conditions needed
by the proof.

The simulation target is a CSLib LTS whose edges are finite abstract executions.
A concrete duplicate send matches an empty execution. Most other steps match
one abstract step. A leader receiving its own token again matches two abstract
steps, `recv` followed by `send`. CSLib's `MTr` and `CanReach` supply these
witnesses. No dissertation-specific simulation predicate is used.

The concrete safety proof depends on the abstract invariant and the simulation;
the dissertation's separate direct concrete VC proofs are not required here.
The namespaces are `RingAbs` and `RingConc` to avoid collisions with existing
tutorial examples.

Build the example and its regression test with:

```sh
lake build Examples.Ring.RingRef VeilTest.CSLibRing
```

The test checks the imported theorem's axioms and a concrete execution on the
ring `[7, 2, 9]`, including duplicate-send stuttering and re-emission of a token
by an existing leader.
