import Veil.State
import Veil.TransitionSystem
import Veil.Tactic
import Veil.DSL
import Examples.DSL.Std

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
  require ¬ configure_round_msg r c
  require tot.le master_complete r
  require complete_of c == master_complete

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
  require cr == complete_of c
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
  require complete_of c == cr
  require ∀ V, ¬ proposal r V
  require ∀ R, tot.le cr R ∧ ¬ tot.le r R → ∃ c, configure_round_msg R c
  require ∀ R C, tot.le cr R ∧ ¬ tot.le r R ∧ configure_round_msg R C → quorumin (quorum_of_round R) C
  require ∀ R N, tot.le cr R ∧ ¬ tot.le r R ∧ member N (quorum_of_round R) → ∃ v, join_ack_msg N r R v
  let mut v : value ← fresh
  let maxr : round ← fresh
  require (v == none ∧ ∀ n mAXR v, ¬ (tot.le cr mAXR ∧ ¬ tot.le r maxr ∧ member n (quorum_of_round mAXR) ∧ join_ack_msg n r mAXR v ∧ v ≠ none)) ∨
          (v ≠ none ∧ (∃ n, tot.le cr maxr ∧ ¬ tot.le r maxr ∧ member n (quorum_of_round maxr) ∧ join_ack_msg n r maxr v ∧ v ≠ none) ∧
          (∀ n mAXR v, (tot.le cr mAXR ∧ ¬ tot.le r mAXR ∧ member n (quorum_of_round mAXR) ∧ join_ack_msg n r mAXR v ∧ v ≠ none) → tot.le mAXR maxr))


  if v == none then
    v ← fresh
    require v ≠ none
    complete_msg r := True
  proposal r v := True
}

action cast_vote (n : node) (v : value) (r : round) = {
  require v ≠ none
  require ¬ (∃ (r' : round) (rp : round) (v' : value), join_ack_msg n r' rp v ∧ ¬ tot.le r' r)
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

safety (decision N1 R1 V1 ∧ decision N2 R2 V2) → V1 = V2

invariant [unique_config] configure_round_msg R C1 ∧ configure_round_msg R C2 → C1 = C2

invariant [property1_one_a] one_a R RP → ¬ tot.le R RP
invariant [property2_one_a] one_a R RP → ∃ c, configure_round_msg R c

invariant [only_vote_proposed] vote N R V → proposal R V

invariant [propose_if_lower_configured] proposal R2 V ∧ tot.le R1 R2 → ∃ c, configure_round_msg R1 c

invariant [master_complete_zero_or_holds] (R2 = master_complete ∨ (configure_round_msg R3 C ∧ complete_of C == R2)) ∧ tot.le R2 R1 → complete_msg R2
invariant [complete_prev_configured] complete_msg R2 ∧ tot.le R1 R2 → ∃ c, configure_round_msg R1 c

-- conjecture forall R:round, V:value. (exists N:node. decision(N,R,V)) -> exists C:config, Q:quorum. configure_round_msg(R,C) & quorumin(Q,C) & (forall N:node. member(N, Q) -> vote(N,R,V))
invariant [decisions_from_quorums] (∃ n, decision n R V) → ∃ c q, configure_round_msg R c ∧ quorumin q c ∧ (∀ n, member n q → vote n R V)

invariant [choosable_proposal] ¬ tot.le R2 R1 ∧ proposal R2 V2 ∧ V1 ≠ V2 ∧ configure_round_msg R1 C ∧ quorumin Q C → ∃ n r3 rp v, member n Q ∧ ¬ tot.le r3 R1 ∧ join_ack_msg n R3 rp V1 ∧ ¬ vote n R1 V1

invariant [configure_round_msg] configure_round_msg R C → tot.le (complete_of C) R ∧ tot.le (complete_of C) master_complete

invariant [complete_choosable_decision] complete_msg RR ∧ ¬ tot.le RR R ∧ configure_round_msg R C ∧ quorumin Q C ∧
          ¬ (∃ n r3 rp vp, member n Q ∧ ¬ tot.le r3 R ∧ join_ack_msg n r3 rp vp ∧ ¬ vote n R V)
          → ∃ nn, decision nn RR V

invariant [none_property1] ¬proposal R none
invariant [none_property2] ¬vote N R none
invariant [none_property3] ¬decision N R none

invariant [join_ack_msg_property1] join_ack_msg N R RP V → one_a R RP
invariant [join_ack_msg_property2] join_ack_msg N R RP V → ¬ vote N RP V
invariant [join_ack_msg_property3] join_ack_msg N R RP V ∧ V ≠ none → vote N RP V

set_option sauto.smt.solver "cvc5"  -- for its determinism

@[invProof]
  theorem init_VerticalPaxosFirstOrder.inv_0 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.inv_0 node node_dec node_ne value value_dec value_ne quorum
                quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.unique_config :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.unique_config node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.property1_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.property1_one_a node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.property2_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.property2_one_a node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.only_vote_proposed :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.only_vote_proposed node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.propose_if_lower_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.propose_if_lower_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.master_complete_zero_or_holds :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.master_complete_zero_or_holds node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.complete_prev_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.complete_prev_configured node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.decisions_from_quorums :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.decisions_from_quorums node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.choosable_proposal :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.choosable_proposal node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.configure_round_msg :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.configure_round_msg node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.complete_choosable_decision :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.complete_choosable_decision node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.none_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.none_property1 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.none_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.none_property2 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.none_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.none_property3 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.join_ack_msg_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.join_ack_msg_property1 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.join_ack_msg_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.join_ack_msg_property2 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_VerticalPaxosFirstOrder.join_ack_msg_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).init
              st →
            (@VerticalPaxosFirstOrder.join_ack_msg_property3 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.inv_0 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.inv_0 node node_dec node_ne value value_dec value_ne quorum
                quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.unique_config :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.unique_config node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.property1_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property1_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.property2_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property2_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.only_vote_proposed :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.only_vote_proposed node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem
    VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.propose_if_lower_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.propose_if_lower_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem
    VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.master_complete_zero_or_holds :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.master_complete_zero_or_holds node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.complete_prev_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_prev_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.decisions_from_quorums :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.decisions_from_quorums node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.choosable_proposal :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.choosable_proposal node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.configure_round_msg :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.configure_round_msg node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem
    VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.complete_choosable_decision :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_choosable_decision node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.none_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property1 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.none_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property2 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.none_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property3 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.join_ack_msg_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property1 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.join_ack_msg_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property2 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.configure_round_VerticalPaxosFirstOrder.join_ack_msg_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.configure_round.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property3 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.configure_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.inv_0 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.inv_0 node node_dec node_ne value value_dec value_ne quorum
                quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.unique_config :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.unique_config node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.property1_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property1_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.property2_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property2_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.only_vote_proposed :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.only_vote_proposed node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem
    VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.propose_if_lower_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.propose_if_lower_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem
    VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.master_complete_zero_or_holds :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.master_complete_zero_or_holds node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.complete_prev_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_prev_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.decisions_from_quorums :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.decisions_from_quorums node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.choosable_proposal :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.choosable_proposal node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.configure_round_msg :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.configure_round_msg node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem
    VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.complete_choosable_decision :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_choosable_decision node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.none_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property1 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.none_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property2 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.none_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property3 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.join_ack_msg_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property1 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.join_ack_msg_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property2 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.mark_complete_VerticalPaxosFirstOrder.join_ack_msg_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.mark_complete.ext node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property3 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.mark_complete.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.inv_0 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.inv_0 node node_dec node_ne value value_dec value_ne quorum
                quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.unique_config :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.unique_config node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.property1_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property1_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.property2_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property2_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.only_vote_proposed :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.only_vote_proposed node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.propose_if_lower_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.propose_if_lower_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.master_complete_zero_or_holds :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.master_complete_zero_or_holds node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.complete_prev_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_prev_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.decisions_from_quorums :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.decisions_from_quorums node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.choosable_proposal :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.choosable_proposal node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.configure_round_msg :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.configure_round_msg node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.complete_choosable_decision :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_choosable_decision node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.none_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property1 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.none_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property2 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.none_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property3 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.join_ack_msg_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property1 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.join_ack_msg_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property2 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.send_1a_VerticalPaxosFirstOrder.join_ack_msg_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.send_1a.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property3 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.send_1a.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.inv_0 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.inv_0 node node_dec node_ne value value_dec value_ne quorum
                quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.unique_config :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.unique_config node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.property1_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property1_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.property2_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property2_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.only_vote_proposed :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.only_vote_proposed node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.propose_if_lower_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.propose_if_lower_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.master_complete_zero_or_holds :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.master_complete_zero_or_holds node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.complete_prev_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_prev_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.decisions_from_quorums :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.decisions_from_quorums node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.choosable_proposal :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.choosable_proposal node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.configure_round_msg :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.configure_round_msg node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.complete_choosable_decision :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_choosable_decision node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.none_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property1 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.none_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property2 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.none_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property3 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.join_ack_msg_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property1 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.join_ack_msg_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property2 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.join_round_VerticalPaxosFirstOrder.join_ack_msg_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.join_round.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property3 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.join_round.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.inv_0 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.inv_0 node node_dec node_ne value value_dec value_ne quorum
                quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.unique_config :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.unique_config node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.property1_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property1_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.property2_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property2_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.only_vote_proposed :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.only_vote_proposed node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.propose_if_lower_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.propose_if_lower_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.master_complete_zero_or_holds :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.master_complete_zero_or_holds node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.complete_prev_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_prev_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.decisions_from_quorums :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.decisions_from_quorums node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.choosable_proposal :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.choosable_proposal node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.configure_round_msg :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.configure_round_msg node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.complete_choosable_decision :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_choosable_decision node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.none_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property1 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.none_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property2 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.none_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property3 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.join_ack_msg_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property1 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.join_ack_msg_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property2 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.propose_VerticalPaxosFirstOrder.join_ack_msg_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.propose.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property3 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.propose.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.inv_0 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.inv_0 node node_dec node_ne value value_dec value_ne quorum
                quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.unique_config :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.unique_config node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.property1_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property1_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.property2_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property2_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.only_vote_proposed :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.only_vote_proposed node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.propose_if_lower_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.propose_if_lower_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.master_complete_zero_or_holds :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.master_complete_zero_or_holds node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.complete_prev_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_prev_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.decisions_from_quorums :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.decisions_from_quorums node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.choosable_proposal :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.choosable_proposal node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.configure_round_msg :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.configure_round_msg node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.complete_choosable_decision :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_choosable_decision node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.none_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property1 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.none_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property2 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.none_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property3 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.join_ack_msg_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property1 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.join_ack_msg_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property2 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.cast_vote_VerticalPaxosFirstOrder.join_ack_msg_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.cast_vote.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property3 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.cast_vote.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.inv_0 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.inv_0 node node_dec node_ne value value_dec value_ne quorum
                quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.unique_config :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.unique_config node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.property1_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property1_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.property2_one_a :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.property2_one_a node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.only_vote_proposed :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.only_vote_proposed node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.propose_if_lower_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.propose_if_lower_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.master_complete_zero_or_holds :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.master_complete_zero_or_holds node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.complete_prev_configured :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_prev_configured node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.decisions_from_quorums :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.decisions_from_quorums node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.choosable_proposal :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.choosable_proposal node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.configure_round_msg :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.configure_round_msg node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.complete_choosable_decision :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.complete_choosable_decision node node_dec node_ne value
                value_dec value_ne quorum quorum_dec quorum_ne round round_dec round_ne config
                config_dec config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.none_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property1 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.none_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property2 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.none_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.none_property3 node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne tot
                st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.join_ack_msg_property1 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property1 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.join_ack_msg_property2 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property2 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext

  @[invProof]
  theorem VerticalPaxosFirstOrder.decide_VerticalPaxosFirstOrder.join_ack_msg_property3 :
      ∀ (st : @State node value quorum round config),
        (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                round_dec round_ne config config_dec config_ne tot).assumptions
            st →
          (@System node node_dec node_ne value value_dec value_ne quorum quorum_dec quorum_ne round
                  round_dec round_ne config config_dec config_ne tot).inv
              st →
            (@VerticalPaxosFirstOrder.decide.ext node node_dec node_ne value value_dec value_ne
                quorum quorum_dec quorum_ne round round_dec round_ne config config_dec config_ne
                tot)
              st fun _ (st' : @State node value quorum round config) =>
              @VerticalPaxosFirstOrder.join_ack_msg_property3 node node_dec node_ne value value_dec
                value_ne quorum quorum_dec quorum_ne round round_dec round_ne config config_dec
                config_ne tot st' :=
    by solve_wlp_clause VerticalPaxosFirstOrder.decide.ext




end VerticalPaxosFirstOrder
