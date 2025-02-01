import Veil.DSL
import Library.Std

-- https://www.wisdom.weizmann.ac.il/~padon/paxos-made-epr-examples.zip /vertical_paxos/vertical_paxos_fol.ivy

namespace VerticalPaxosFirstOrder
open Classical

type node
type value
type quorum
type round
type config

individual none : value
instantiate tot : TotalOrder round

immutable relation member (N : node) (Q: quorum)
immutable relation quorumin (Q : quorum) (C : config)

relation one_a (R1 : round) (R2 : round)
relation join_ack_msg (N : node) (R1 : round) (R2 : round) (V : value)
relation proposal (R : round) (V : value)
relation vote (N : node) (R : round) (V : value)
relation decision (N : node) (R : round) (V : value)
relation configure_round_msg (R : round) (C : config)
relation complete_msg (R : round)
function complete_of (C : config) : round
function quorum_of_round (R : round) : quorum
individual master_complete : round

#gen_state

assumption ∀ (c : config) (q1 : quorum) (q2 : quorum), quorumin q1 c ∧ quorumin q2 c → ∃ (n : node), member n q1 ∧ member n q2

after_init {
  one_a R1 R2 := False;
  join_ack_msg N R1 R2 V := False;
  proposal R V := False;
  vote N R V := False;
  decision N R V := False;
  configure_round_msg R C := False;
  complete_msg R := False;
  require ∀ R, tot.le master_complete R
}

-- master action
action configure_round (r : round) (c : config) = {
  require ∀ C, ¬ configure_round_msg r C
  require tot.le master_complete r
  require complete_of c = master_complete

  configure_round_msg r c := True
}

action mark_complete (r : round) = {
  require complete_msg r
  if ¬ tot.le r master_complete then
    master_complete := r
}

-- nodes actions
action send_1a (r : round) (c : config) (cr : round) = {
  require configure_round_msg r c
  require cr = complete_of c
  one_a r R := one_a r R ∨ (tot.le cr R ∧ ¬ tot.le r R)
 }

 action join_round (n : node) (r : round) (rp : round) = {
  require one_a r rp
  require ¬ (∃ r' rp' v, join_ack_msg n r' rp' v ∧ ¬ tot.le r' r)
  let mut v : value ← fresh
  if ∀ V, ¬ vote n rp V then
    v := none
  else
    require vote n rp v
  join_ack_msg n r rp v := True
 }

action propose (r : round) (c : config) (cr : round) = {
  quorum_of_round R := *
  require configure_round_msg r c
  require complete_of c = cr
  require ∀ V, ¬ proposal r V
  require ∀ R, tot.le cr R ∧ ¬ tot.le r R → ∃ c, configure_round_msg R c
  require ∀ R C, tot.le cr R ∧ ¬ tot.le r R ∧ configure_round_msg R C → quorumin (quorum_of_round R) C
  require ∀ R N, tot.le cr R ∧ ¬ tot.le r R ∧ member N (quorum_of_round R) → ∃ v, join_ack_msg N r R v
  let mut v : value ← fresh
  let maxr : round ← fresh
  assume ((v = none ∧ forall N MAXR V,
                      ¬ (tot.le cr MAXR ∧ ¬tot.le r MAXR ∧ member N (quorum_of_round MAXR)) ∧ join_ack_msg N r MAXR V ∧ V ≠ none) ∨
                      (v ≠ none ∧
                      (exists N:node, tot.le cr maxr ∧ ¬tot.le r maxr ∧ member N (quorum_of_round maxr) ∧ join_ack_msg N r maxr v ∧ v ≠ none) ∧
                      (forall N MAXR V,
                       (tot.le cr MAXR  ∧ ¬tot.le r MAXR ∧ member N (quorum_of_round MAXR) ∧ join_ack_msg N r MAXR V ∧ V ≠ none) -> tot.le MAXR maxr)
                    ));
  if v = none then
    v := *
    require v ≠ none
    complete_msg r := True
  proposal r v := True
}

action cast_vote (n : node) (v : value) (r : round) = {
  require v ≠ none
  require ¬ (∃ (r' : round) (rp : round) (v' : value), join_ack_msg n r' rp v' ∧ ¬ tot.le r' r)
  require proposal r v
  vote n r v := True
}

action decide (n : node) (r : round) (c : config) (v : value) (q : quorum) = {
  require v ≠ none
  require configure_round_msg r c
  require quorumin q c
  require ∀ N, member N q → vote N r v
  decision n r v := True
  complete_msg r := True
}

safety [coherence] (decision N1 R1 V1 ∧ decision N2 R2 V2) → V1 = V2

invariant [proposal_unique] proposal R V1 ∧ proposal R V2 → V1 = V2

invariant [unique_config] configure_round_msg R C1 ∧ configure_round_msg R C2 → C1 = C2

invariant [property1_one_a] one_a R RP → ¬ tot.le R RP
invariant [property2_one_a] one_a R RP → ∃ c, configure_round_msg R c

invariant [only_vote_proposed] vote N R V → proposal R V

invariant [propose_if_lower_configured] proposal R2 V ∧ tot.le R1 R2 → ∃ c, configure_round_msg R1 c

invariant [master_complete_zero_or_holds] (R2 = master_complete ∨ (configure_round_msg R3 C ∧ complete_of C = R2)) ∧ ¬ tot.le R2 R1 → complete_msg R2
invariant [complete_prev_configured] complete_msg R2 ∧ tot.le R1 R2 → ∃ c, configure_round_msg R1 c

-- conjecture forall R:round, V:value. (exists N:node. decision(N,R,V)) -> exists C:config, Q:quorum. configure_round_msg(R,C) & quorumin(Q,C) & (forall N:node. member(N, Q) -> vote(N,R,V))
invariant [decisions_from_quorums] (∃ n, decision n R V) → ∃ c q, configure_round_msg R c ∧ quorumin q c ∧ (∀ n, member n q → vote n R V)

invariant [choosable_proposal] ¬ tot.le R2 R1 ∧ proposal R2 V2 ∧ V1 ≠ V2 ∧
  configure_round_msg R1 C ∧ quorumin Q C → ∃ n r3 rp v, member n Q ∧ ¬ tot.le r3 R1 ∧ join_ack_msg n r3 rp v ∧ ¬ vote n R1 V1

invariant [configure_round_msg] configure_round_msg R C → tot.le (complete_of C) R ∧ tot.le (complete_of C) master_complete

invariant [complete_choosable_decision] complete_msg RR ∧ ¬ tot.le RR R ∧ configure_round_msg R C ∧ quorumin Q C ∧
          ¬ (∃ n r3 rp vp, member n Q ∧ ¬ tot.le r3 R ∧ join_ack_msg n r3 rp vp ∧ ¬ vote n R V)
          → ∃ nn, decision nn RR V

invariant [none_property1] ¬proposal R none
invariant [none_property2] ¬vote N R none
invariant [none_property3] ¬decision N R none

invariant [join_ack_msg_property1] join_ack_msg N R RP V → one_a R RP
invariant [join_ack_msg_property2] join_ack_msg N R RP none → ¬ vote N RP V
invariant [join_ack_msg_property3] join_ack_msg N R RP V ∧ V ≠ none → vote N RP V

#gen_spec

set_option sauto.smt.solver "cvc5"  -- for its determinism

#time #check_invariants_wlp

end VerticalPaxosFirstOrder
