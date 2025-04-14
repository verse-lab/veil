import Veil

-- https://www.wisdom.weizmann.ac.il/~padon/paxos-made-epr-examples.zip /paxos/paxos_fol.ivy

veil module PaxosFirstOrder

type node
type value
type quorum
type round

individual none : round
instantiate tot : TotalOrder round

immutable relation member (N : node) (Q: quorum)


relation one_a (R:round)
relation one_b_max_vote (N:node) (R1:round) (R2:round) (V:value)
relation proposal (R:round) (V:value) -- 2a
relation vote (N:node) (R:round) (V:value) -- 2b
relation decision (N:node) (R:round) (V:value) -- got 2b from a quorum


#gen_state
assumption ∀ (Q1:quorum) (Q2:quorum), ∃ (N:node), member N Q1 ∧ member N Q2


after_init {
  one_a R := False;
  one_b_max_vote N R1 R2 V := False;
  proposal R V := False;
  vote N R V := False;
  decision N R V := False
}


action send_1a = {
  -- a proposer selects a round and sends a message asking nodes to join the round
  let r : round ← fresh
  require r ≠ none;
  one_a r := True
}

action join_round (n:node) (r:round) = {
    -- receive 1a and answer with 1b
    require r ≠ none;
    require one_a r;
    require ¬(∃ (r':round) (rMAX:round) (v:value), one_b_max_vote n r' rMAX v ∧ ¬ tot.le r' r);
    let maxr : round ← fresh
    let v : value ← fresh
      -- find the maximal vote in a round less than r
    require ((maxr = none ∧ ∀ (mAXR:round) (v':value), ¬ (¬ tot.le r mAXR ∧ vote n mAXR v')) ∨
                    (maxr ≠ none ∧ ¬ tot.le r maxr ∧ vote n maxr v ∧
                    (∀ (mAXR:round) (v':value), (¬ tot.le r mAXR ∧ vote n mAXR v') -> tot.le mAXR maxr)
                   ));
    -- send the 1b message
    one_b_max_vote n r maxr v := True
}

action propose (r : round) (q: quorum) = {
    -- receive a quorum of 1b's and send a 2a (proposal)
    require r ≠ none;
    require ∀ V, ¬ proposal r V;
    require ∀ (n:node), member n q -> ∃ (r':round) (v:value), one_b_max_vote n r r' v;
    let maxr : round ← fresh
    let v : value ← fresh
    -- find the maximal max_vote in the quorum
    require ((maxr = none ∧ ∀ (n:node) (mAXR:round) (v:value), ¬ (member n q ∧ one_b_max_vote n r mAXR v ∧ mAXR ≠ none)) ∨
                    (maxr ≠ none ∧
                    (∃ (n:node), member n q ∧ one_b_max_vote n r maxr v) ∧
                    (∀ (n:node) (mAXR:round) (v:value), (member n q ∧ one_b_max_vote n r mAXR v ∧ mAXR ≠ none) -> tot.le mAXR maxr)
                    ));
    -- propose value v
    proposal r v := True

}

action cast_vote (n:node) (v:value) (r:round) = {
    -- receive a 2a and send 2b
    require r ≠ none;
    require ¬(∃ (r':round) (rMAX:round) (v':value), one_b_max_vote n r' rMAX v' ∧ ¬ tot.le r' r);
    require proposal r v;
    vote n r v := True
}

action decide (n:node) (r:round) (v:value) (q:quorum) = {
    -- get 2b from a quorum
    require r ≠ none;
    require ∀ N, member N q -> vote N r v;
    decision n r v := True
}

safety [coherence] (decision N1 R1 V1 ∧ decision N2 R2 V2) → V1 = V2

invariant [unique_proposals] (proposal R V1 ∧ proposal R V2) → V1 = V2

invariant [vote_proposal] (vote N R V) → proposal R V

invariant [decision_from_quorum] (∀ (R:round) (V:value), (∃ (N:node), decision N R V) → (∃ (Q:quorum), ∀ (N:node), member N Q → vote N R V))

invariant [one_b_max_vote_properties1] (one_b_max_vote N R2 none V1 ∧ ¬ tot.le R2 R1) → ¬ vote N R1 V2

invariant [one_b_max_vote_properties2] (one_b_max_vote N R RMAX V ∧ RMAX ≠ none) → ¬ tot.le R RMAX ∧ vote N RMAX V

invariant [one_b_max_vote_properties3] (one_b_max_vote N R RMAX V ∧ RMAX ≠ none ∧ ¬ tot.le R ROTHER ∧ ¬ tot.le ROTHER RMAX) → ¬ vote N ROTHER VOTHER

invariant [none_vote] ¬ vote N none V

invariant [choosable_proposal] (∀ (R1:round) (R2:round) (V1:value) (V2:value) (Q:quorum), ¬ tot.le R2 R1 ∧ proposal R2 V2 ∧ V1 ≠ V2 →
    (∃ (N:node) (R3:round) (RMAX:round) (V:value), member N Q ∧ ¬ tot.le R3 R1 ∧ one_b_max_vote N R3 RMAX V ∧ ¬ vote N R1 V1))

#gen_spec

#time #check_invariants

end PaxosFirstOrder
