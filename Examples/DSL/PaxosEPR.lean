import Veil.State
import Veil.TransitionSystem
import Veil.Tactic
import Veil.DSL
import Examples.DSL.Std

-- https://github.com/dranov/protocol-specs/blob/main/Paxos/paxos_epr.ivy

namespace PaxosEPR
open Classical

type node
type value
type quorum
type round

individual none : round
instantiate tot : TotalOrder round

immutable relation member (N : node) (Q: quorum)

relation one_a (R:round)
relation one_b_max_vote (N:node) (R1:round) (R2:round) (V:value)
relation one_b (N:node) (R:round)
relation left_rnd (N:node) (R:round)
relation proposal (R:round) (V:value) -- 2a
relation vote (N:node) (R:round) (V:value) -- 2b
relation decision (N:node) (R:round) (V:value) -- got 2b from a quorum

#gen_state

after_init {
  one_a R := False
  one_b_max_vote N R1 R2 V := False
  one_b N R := False
  left_rnd N R := False
  proposal R V := False
  vote N R V := False
  decision N R V := False
}

assumption ∀ (Q1:quorum) (Q2:quorum), ∃ (N:node), member N Q1 ∧ member N Q2

action send_1a (r : round) = {
  -- a proposer selects a round and sends a message asking nodes to join the round
  require r ≠ none
  one_a r := True
}

action join_round (n:node) (r:round) = {
    -- receive 1a and answer with 1b
    require r ≠ none
    require one_a r
    require ¬ left_rnd n r
    let maxr : round ← fresh
    let v : value ← fresh
      -- find the maximal vote in a round less than r
    require (maxr = none ∧ ∀ (mAXR:round) (v':value), ¬ (¬ tot.le r mAXR ∧ vote n mAXR v')) ∨
                    (maxr ≠ none ∧ ¬ tot.le r maxr ∧ vote n maxr v ∧
                    (∀ (mAXR:round) (v':value), (¬ tot.le r mAXR ∧ vote n mAXR v') -> tot.le mAXR maxr))
    one_b_max_vote N R maxr v := True
    one_b N R := True
    left_rnd N K := left_rnd N K ∨ (¬ tot.le r K)
}

action propose (r : round) (q : quorum) = {
  require r ≠ none
  require ∀ V, ¬ proposal r V
  require ∀ (N:node), member N q -> one_b N r
  let maxr : round ← fresh
  let v : value ← fresh
      -- find the maximal vote in a round less than r
  require ∀ N, (maxr = none ∧ ∀ (n : node) (mAXR:round) (v':value), ¬ (member n q ∧ ¬ tot.le r mAXR ∧ vote n mAXR v')) ∨
                    (maxr ≠ none ∧
                    (∃ (n : node), member n q ∧ ¬ tot.le r maxr ∧ vote n maxr v) ∧
                    (∀ (n : node) (mAXR:round) (v':value), (member n q ∧ ¬ tot.le r mAXR ∧ vote N mAXR v') -> tot.le mAXR maxr))
  proposal R v := True
}

action cast_vote (n:node) (v:value) (r:round) = {
  require r ≠ none
  require ¬ left_rnd n r
  require proposal r v
  vote n r v := True
}

action decide (n:node) (r:round) (v:value) (q : quorum) = {
  require r ≠ none
  require ∀ N, member N q → vote N r v
  decision n r v := True
}

safety [coherence] decision N1 R1 V1 ∧ decision N2 R2 V2 → V1 = V2


-- # proposals are unique per round
invariant [unique_proposals] proposal R V1 ∧ proposal R V2 -> V1 = V2

-- # only vote for proposed values
invariant [vote_proposed] vote N R V -> proposal R V

-- # decisions come from quorums of votes:
invariant ∀ (R:round) (V:value), (∃ n:node, decision n R V)
       -> ∃ (q:quorum), ∀ N:node, member N q -> vote N R V

-- # properties of one_b_max_vote
-- invariant one_b_max_vote(N,R2,none,V1) & ~le(R2,R1) -> ~vote(N,R1,V2)
-- invariant one_b_max_vote(N,R,RMAX,V) & RMAX ~= none -> ~le(R,RMAX) & vote(N,RMAX,V)
-- invariant one_b_max_vote(N,R,RMAX,V) & RMAX ~= none & ~le(R,ROTHER) & ~le(ROTHER,RMAX) -> ~vote(N,ROTHER,VOTHER)

-- # properties of none
invariant [none_prop] ¬ vote N none V

-- # Properties of choosable and proposal
invariant [choosable_proposal] ∀ (R1:round) (R2:round) (V1:value) (V2:value) (Q:quorum), ¬ tot.le R2 R1 ∧ proposal R2 V2 ∧ V1 ≠ V2 ->
    ∃ n:node, member n Q ∧ left_rnd n R1 ∧ ¬vote n R1 V1

-- # properties of one_b, left_rnd
-- #conjecture one_b_max_vote(N,R,RMAX,V) -> one_b(N,R)
invariant [oneb_leftrnd] one_b N R2 ∧ ¬tot.le R2 R1 -> left_rnd N R1

#gen_spec

#check_invariants


end PaxosEPR
