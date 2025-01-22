import Veil.DSL
import Examples.DSL.Std
-- https://github.com/aman-goel/ivybench/blob/master/paxos/ivy/oopsla17_flexible_paxos.ivy


namespace FlexiblePaxos
open Classical

type round
type value
type quorum_1
type quorum_2
type node

instantiate tot : TotalOrder round

immutable individual negone : round
immutable individual max_ : round

immutable relation member_1 : node -> quorum_1 -> Prop
immutable relation member_2 : node -> quorum_2 -> Prop

relation one_a : round -> Prop
relation one_b_max_vote : node -> round -> round -> value -> Prop
relation one_b : node → round → Prop
relation left_rnd : node → round → Prop
relation proposal : round -> value -> Prop
relation vote : node -> round -> value -> Prop
relation decision : node -> round -> value -> Prop

relation isSafeAtPaxos : round → value → Prop

#gen_state

ghost relation chosenAt (R : round) (V : value) := ∃ q, ∀ n, member_2 n q → vote n R V
ghost relation showsSafeAtPaxos (Qin : quorum_1) (Rin : round) (Vin : value) := (∀ n, member_1 n Qin → one_b n Rin) ∧
    (
      ∃ maxRin, (maxRin = negone ∧ ∀ (n : node) (maxR: round) (v : value), ¬ (member_1 n Qin ∧ ¬ tot.le Rin maxR ∧ vote n maxR v)) ∨
                (maxRin ≠ negone ∧ (∃ (n : node), member_1 n Qin ∧ ¬ tot.le Rin maxRin ∧ vote n maxRin Vin) ∧
                                   (∀ (n : node) (maxR : round) (v : value), (member_1 n Qin ∧ ¬ tot.le Rin maxR ∧ vote n maxR v) → tot.le maxR maxRin))
    )
assumption ∀ (x : round), tot.le negone x
assumption ∀ (x : round), tot.le x max_
assumption ∀ (q₁ : quorum_1) (q₂ : quorum_2), ∃ (n : node), member_1 n q₁ ∧ member_2 n q₂

after_init {
  one_a R := False;
  one_b N R := False;
  one_b_max_vote N R1 R2 V := False;
  left_rnd N R := False;
  proposal R V := False;
  vote N R V := False;
  decision N R V := False
}

action send_1a = {
  let r <- fresh
  require r ≠ negone;
  one_a r := True
}

action join_round = {
  let n <- fresh node
  let r <- fresh round
  require r ≠ negone;
  require one_a r;
  require ¬ left_rnd n r;
  let max_r <- fresh round
  let v <- fresh value
  require ((max_r = negone ∧ ∀ maxR v, ¬ (¬ (tot.le r maxR) ∧ vote n maxR v)) ∨
    (max_r ≠ negone ∧ ¬ tot.le r max_r ∧ vote n max_r v ∧ (∀ maxR v, (¬ tot.le r maxR ∧ vote n maxR v) → tot.le maxR max_r)));
  one_b_max_vote n r max_r v := True;
  one_b n r := True;
  left_rnd n R := left_rnd n R ∨ ¬ tot.le r R
}

action propose = {
  let r <- fresh round
  let v <- fresh value
  require r ≠ negone;
  require ∀ V, ¬ proposal r V;
  require ∀ V, isSafeAtPaxos r V;
  proposal r v := True
}

action cast_vote = {
  let n <- fresh node
  let v <- fresh value
  let r <- fresh round
  require r ≠ negone;
  require ¬ left_rnd n r;
  require proposal r v;
  vote n r v := True
}

action decide = {
  let n <- fresh node
  let r <- fresh round
  let v <- fresh value
  require r ≠ negone;
  require chosenAt r v;
  decision n r v := True
}

safety [coherence] (decision N1 R1 V1 ∧ decision N2 R2 V2) -> V1 = V2
invariant [ic3po_other2] ∀ V1 R1, ¬ proposal R1 V1 ∨ isSafeAtPaxos R1 V1
invariant [ic3po_other5] ∀ V1 R1 N1, ¬ vote N1 R1 V1 ∨ proposal R1 V1
invariant [ic3po_other6] ∀ N1 R1 V1, ¬ decision N1 R1 V1 ∨ chosenAt R1 V1
invariant [ic3po_other8] ∀ N1 R1 R2, ¬ one_b N1 R2 ∨ left_rnd N1 R1 ∨ tot.le R2 R1
invariant [ic3po_other10] ∀ R1 V1 V2, V1 = V2 ∨ ¬ proposal R1 V1 ∨ ¬ proposal R1 V2


-- invariant [swiss] ∀ R V1 V2, proposal R V1 ∧ proposal R V2 -> V1 = V2
-- invariant [vote_proposed] ∀ N R V, vote N R V -> proposal R V
-- invariant [decision_from_votes] ∀ R V, (∃ N, decision N R V) -> (∃ Q, ∀ N, member_2 N Q -> vote N R V)
-- invariant [no_vote_negone] ∀ N V, ¬ vote N negone V
-- invariant [one_b_implies_one_b_max_vote] one_b_max_vote N R RMAX V -> one_b N R
-- invariant [one_b_implies_left_rnd] one_b N R2 ∧ ¬ tot.le R2 R1 -> left_rnd N R1
-- invariant [one_b_max_vote_implies_no_vote] one_b_max_vote N R2 negone V1 ∧ ¬ tot.le R2 R1 -> ¬ vote N R1 V2
-- invariant [one_b_max_vote_implies_vote] one_b_max_vote N R RMAX V ∧ RMAX ≠ negone -> ¬ tot.le R RMAX ∧ vote N RMAX V
-- invariant [one_b_max_vote_implies_no_vote_other] one_b_max_vote N R RMAX V ∧ ¬ tot.le R ROTHER ∧ ¬ tot.le ROTHER RMAX -> ¬ vote N ROTHER VOTHER


#gen_spec

#check_invariants

end FlexiblePaxos
