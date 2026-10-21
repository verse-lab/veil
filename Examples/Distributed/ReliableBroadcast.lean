module

public import Veil

/-! # Bracha's Byzantine reliable broadcast, as a node program

The protocol of `Examples/Ivy/ReliableBroadcast.lean`, written as the program
each node runs (see `docs/Distributed-DSL.md`), and verified with SMT.

A designated `originator` broadcasts a value. Out of `n = 3f + 1` nodes, at
most `f` are Byzantine (the originator may be one of them). Each node:

- **echoes** the first value it receives from the originator;
- **votes** for a value once it has seen echoes for it from a supermajority
  (`2f + 1` nodes), or votes for it from more than a third (`f + 1` nodes);
- **delivers** a value once it has seen votes for it from a supermajority.

Guarantees, for honest nodes:

- *agreement*: no two honest nodes deliver different values, even if the
  originator is Byzantine;
- *integrity*: if the originator is honest, honest nodes only deliver its
  value.

Who is Byzantine, and the quorum facts the proof needs, come from Veil's
`ByzNodeSet` class: two supermajorities intersect in an honest node, and a set
of more than a third of the nodes contains an honest one.
-/

veil module DistReliableBroadcast

type node
type nodeset
type value
instantiate nset : ByzNodeSet node nodeset
open ByzNodeSet

immutable individual originator : node
immutable individual input : value

network (synchrony := async) (faults := byzantine is_byz)

message initial (v : value)
message echo (v : value)
message vote (v : value)

var echoed : value → Bool := fun _ => false
var voted : value → Bool := fun _ => false
var delivered : value → Bool := fun _ => false
-- who this node has received an echo / a vote for each value from
var echoFrom : value → node → Bool := fun _ _ => false
var voteFrom : value → node → Bool := fun _ _ => false

program (self : node) {
  if self = originator then
    broadcast (initial input)
  repeat
    recv
    | (initial v) from s =>
      if s = originator ∧ ¬ (∃ w, echoed w) then
        echoed v := true
        broadcast (echo v)
    | (echo v) from s => echoFrom v s := true
    | (vote v) from s => voteFrom v s := true
    if ¬ (∃ w, voted w) ∧ ∃ v,
        (∃ q, nset.supermajority q ∧ ∀ s, member s q → echoFrom v s) ∨
        (∃ q, nset.greater_than_third q ∧ ∀ s, member s q → voteFrom v s) then
      let v :|
        (∃ q, nset.supermajority q ∧ ∀ s, member s q → echoFrom v s) ∨
        (∃ q, nset.greater_than_third q ∧ ∀ s, member s q → voteFrom v s)
      voted v := true
      broadcast (vote v)
    if ∃ v q, nset.supermajority q ∧ ∀ s, member s q → voteFrom v s then
      let v :| ∃ q, nset.supermajority q ∧ ∀ s, member s q → voteFrom v s
      delivered v := true
}

safety [agreement]
  ¬ is_byz A ∧ ¬ is_byz B ∧ delivered A V1 ∧ delivered B V2 → V1 = V2
safety [integrity]
  ¬ is_byz originator ∧ ¬ is_byz N ∧ delivered N V → V = input

-- An honest originator only sends its input.
invariant [honest_initial] ¬ is_byz originator → initial_net originator D V → V = input
-- An echo or vote attributed to an honest node, whether still in flight or
-- already recorded by its receiver, was really sent by it.
invariant [echo_sent] ¬ is_byz S → (echo_net S D V ∨ echoFrom D V S) → echoed S V
invariant [vote_sent] ¬ is_byz S → (vote_net S D V ∨ voteFrom D V S) → voted S V
-- Honest nodes echo and vote at most once.
invariant [echo_once] ¬ is_byz N → echoed N V1 ∧ echoed N V2 → V1 = V2
invariant [vote_once] ¬ is_byz N → voted N V1 ∧ voted N V2 → V1 = V2
-- Why an honest node echoed, voted or delivered.
invariant [echo_input] ¬ is_byz originator ∧ ¬ is_byz N ∧ echoed N V → V = input
invariant [vote_input] ¬ is_byz originator ∧ ¬ is_byz N ∧ voted N V → V = input
invariant [delivered_quorum]
  ¬ is_byz N → delivered N V → ∃ q, nset.supermajority q ∧ ∀ s, member s q → voteFrom N V s

#gen_spec

#check_invariants

end DistReliableBroadcast
