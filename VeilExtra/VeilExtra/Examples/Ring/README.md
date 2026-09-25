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

The simulation uses CSLib's `LTS.saturate` and `STr`, with `send` classified as
internal (`τ`) and `recv` as the visible `receive` event. A duplicate concrete
send matches zero abstract steps. Most other steps match one abstract step.
A leader receiving its own token again matches `recv` followed by internal
`send`. Each visible receive therefore matches exactly one abstract receive,
with internal sends permitted before and after it. The observation hides the
receive parameters; the state relation connects the actual messages.

CSLib's `IsSimulation.isSimulation_saturate_left` also gives a simulation of both
saturated systems. `sim_trace` preserves finite observed traces in the saturated
target. No dissertation-specific simulation predicate is used. These results
establish safety and finite-trace matching, without a fairness or eventual-election
claim.

The concrete safety proof depends on the abstract invariant and the simulation;
the dissertation's separate direct concrete VC proofs are not required here.
The namespaces are `RingAbs` and `RingConc` to avoid collisions with existing
tutorial examples.

From the repository root, build the example with:

```sh
lake -d VeilExtra build VeilExtra.Examples.Ring.RingRef
```
