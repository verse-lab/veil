import Veil.DSL
import Examples.DSL.PaxosDSL
-- https://github.com/aman-goel/ivybench/blob/master/paxos/ivy/oopsla17_flexible_paxos.ivy


section FlexiblePaxos
open Classical

type round
type value
type quorum_1
type quorum_2
type node

instantiate tot : TotalOrder round

individual negone : round
individual max : round

relation member_1 : node -> quorum_1 -> Prop
relation member_2 : node -> quorum_2 -> Prop

relation one_a : round -> Prop
relation one_b_max_vote : node -> round -> round -> value -> Prop
relation one_b : node → round → Prop
relation left_rnd : node → round → Prop
relation proposal : round -> value -> Prop
relation vote : node -> round -> value -> Prop
relation decision : node -> round -> value -> Prop

relation chosenAt : round -> value -> Prop
relation showsSafeAtPaxos : quorum_1 → round → value → Prop
relation isSafeAtPaxos : round → value → Prop

#gen_state FlexiblePaxos

after_init {
  one_a _ := False;
  one_b _ _ := False;
  one_b_max_vote _ _ _ _ := False;
  left_rnd _ _ := False;
  proposal _ _ := False;
  vote _ _ _ := False;
  decision _ _ _ := False;
  fresh negone' : round in
  fresh max' : round in
  negone := negone';
  max := max';
  require ∀ (Q1 : quorum_1) (Q2 : quorum_2), ∃ (N : node), member_1 N Q1 ∧ member_2 N Q2; -- axiom
  require ∀ (X : round), tot.le negone' X; -- axiom
  require ∀ (X : round), tot.le X max'; -- axiom
  require ∀ r v, (chosenAt r v) ↔ (∃ q, ∀ n, member_2 n q → vote n r v);  -- definition
  require ∀ Qin Rin Vin, (showsSafeAtPaxos Qin Rin Vin) ↔ (∀ n, member_1 n Qin → one_b n Rin) ∧
    ∃ maxRin, (maxRin ≠ negone ∧ (∃ n, member_1 n Qin ∧ ¬ tot.le Rin maxRin ∧ vote n maxRin Vin) ∧
    (∀ n maxR v, (member_1 n Qin ∧ ¬ tot.le Rin maxR ∧ vote n maxR v → tot.le maxR maxRin)) )
}

action send_1a = {
  fresh r : round in
  require r ≠ negone;
  one_a r := True
}

action join_round = {
  fresh n : node in
  fresh r : round in
  require r ≠ negone;
  require one_a r;
  require ¬ left_rnd n r;
  fresh max_r : round in
  fresh v : value in
  require ((max_r = negone ∧ ∀ maxR v, ¬ (¬ (tot.le r maxR) ∧ vote n maxR v)) ∨
    (max_r ≠ negone ∧ ¬ tot.le r max_r ∧ vote n max_r v ∧ (∀ maxR v, (¬ tot.le r maxR ∧ vote n maxR v) → tot.le maxR max_r)));
  one_b_max_vote n r max_r v := True;
  one_b n r := True;
  left_rnd n R := left_rnd n R ∨ ¬ tot.le r R
}

action propose = {
  fresh r : round in
  fresh v : value in
  require r ≠ negone;
  require ¬ proposal r V;
  require isSafeAtPaxos r V;
  proposal r v := True
}

action cast_vote = {
  fresh n : node in
  fresh v : value in
  fresh r : round in
  require r ≠ negone;
  require ¬ left_rnd n r;
  require proposal r v;
  vote n r v := True
}

action decide = {
  fresh n : node in
  fresh r : round in
  fresh v : value in
  require r ≠ negone;
  require chosenAt r v;
  decision n r v := True
}

safety (decision N1 R1 V1 ∧ decision N2 R2 V2) -> V1 = V2
invariant [ic3po_other2] ∀ V1 R1, ¬ proposal R1 V1 ∨ isSafeAtPaxos R1 V1
invariant [ic3po_other5] ∀ V1 R1 N1, ¬ vote N1 R1 V1 ∨ proposal R1 V1
invariant [ic3po_other6] ∀ N1 R1 V1, ¬ decision N1 R1 V1 ∨ chosenAt R1 V1
invariant [ic3po_other8] ∀ N1 R1 R2, ¬ one_b N1 R2 ∨ left_rnd N1 R1 ∨ tot.le R2 R1
invariant [ic3po_other10] ∀ R1 V1 V2, V1 = V2 ∨ ¬ proposal R1 V1 ∨ ¬ proposal R1 V2

#gen_spec FlexiblePaxos

#check_invariants

end FlexiblePaxos
