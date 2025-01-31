import Veil.State
import Veil.TransitionSystem
import Veil.Tactic
import Veil.DSL
import Examples.DSL.Std

import Veil.DSL.InvariantManipulation

-- adapted from [weak_mvc.ivy](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/ivy/weak_mvc.ivy)

class ThreeValuedType (t : Type) where
  v0 : t
  v1 : t
  vquestion : t

  -- axioms
  ax1 : v0 ≠ v1
  ax2 : v0 ≠ vquestion
  ax3 : v1 ≠ vquestion
  ax4 : ∀ (x : t), x = v0 ∨ x = v1 ∨ x = vquestion

class Rabia.Background (node set_majority set_f_plus_1 : outParam Type) where
  member_maj : node → set_majority → Prop
  member_fp1 : node → set_f_plus_1 → Prop

  ax0 : ∀ (Q1 Q2 : set_majority), ∃ (N : node), member_maj N Q1 ∧ member_maj N Q2
  ax1 : ∀ (Q1 : set_majority) (Q2 : set_f_plus_1), ∃ (N : node), member_maj N Q1 ∧ member_fp1 N Q2
namespace Rabia
open Classical

set_option veil.gen_sound true
set_option synthInstance.maxSize 1000000

type node
type set_majority
type set_f_plus_1
instantiate bg : Background node set_majority set_f_plus_1

type phase
instantiate tot : TotalOrderWithMinimum phase

relation in_phase : node → phase → Prop

type proposal_value
type state_value
-- poor man's enum type
instantiate tv : ThreeValuedType state_value

open ThreeValuedType TotalOrderWithMinimum Background

relation propose : node → proposal_value → Prop
relation vote_rnd1 : node → phase → state_value → Prop
relation vote_rnd2 : node → phase → state_value → Prop

relation decision_bc : node → phase → state_value → Prop
relation decision_full_val : node → phase → proposal_value → Prop
relation decision_full_noval : node → phase → Prop
relation coin : phase → state_value → Prop

#gen_state

after_init {
  in_phase N P := False;
  decision_bc N P V := False;
  decision_full_val N P V := False;
  decision_full_noval N P := False;
  propose N V := False;
  vote_rnd1 N P V := False;
  vote_rnd2 N P V := False;
  coin P V := False
}

action initial_proposal = {
  let n : node ← fresh
  let v : proposal_value ← fresh
  assume ¬ ∃ V : proposal_value, propose n V
  assume ∀ P, ¬ ∃ V : state_value, vote_rnd1 n P V
  assume ∀ P, ¬ ∃ V : state_value, vote_rnd2 n P V
  assume ∀ P, ¬ ∃ V : state_value, decision_bc n P V
  assume ∀ P, ¬ in_phase n P
  propose n v := True
}

action decide_bc_decide_full_val = {
  let n : node ← fresh
  let p : phase ← fresh
  let q : set_majority ← fresh
  assume decision_bc n p v1
  if v : (∀ (N : node), member_maj N q → propose N v) then
    decision_full_val n p v := True
}

action decide_bc_decide_full_noval = {
  let n : node ← fresh
  let p : phase ← fresh
  assume decision_bc n p v0
  decision_full_noval n p := True
}

action initial_vote1 = {
  let n : node ← fresh
  let q : set_majority ← fresh
  assume ∃ V : proposal_value, propose n V
  assume ∀ P, ¬ ∃ V : state_value, vote_rnd1 n P V
  assume ∀ P, ¬ ∃ V : state_value, vote_rnd2 n P V
  assume ∀ P, ¬ ∃ V : state_value, decision_bc n P V
  assume ∀ P, ¬ in_phase n P

  if v : (∀ (N : node), member_maj N q → propose N v) then
    vote_rnd1 n zero v1 := True
    in_phase n zero := True
  else
    vote_rnd1 n zero v0 := True
    in_phase n zero := True
}

action phase_rnd1 = {
  let n : node ← fresh
  let p : phase ← fresh
  let q : set_majority ← fresh
  assume in_phase n p
  assume ¬ ∃ V : state_value, vote_rnd2 n p V
  assume ∀ (N : node), member_maj N q → ∃ V, vote_rnd1 N p V

  if v : (∀ (N : node), member_maj N q → vote_rnd1 N p v) then
    vote_rnd2 n p v := True
  else
    vote_rnd2 n p vquestion := True
}

action phase_rnd2 = {
  let n : node ← fresh
  let p : phase ← fresh
  let psucc : phase ← fresh
  let q : set_majority ← fresh
  assume in_phase n p
  assume ∃ V : state_value, vote_rnd2 n p V
  assume ∀ (N : node), member_maj N q → ∃ V, vote_rnd2 N p V
  assume next p psucc

  if v : (v ≠ vquestion ∧
      (∃ N0 Q, member_fp1 N0 Q ∧ (∀ N, member_fp1 N Q → member_maj N q ∧ vote_rnd2 N p v)))
  then
    decision_bc n p v := True
    vote_rnd1 n psucc v := True
    in_phase n psucc := True
    in_phase n p := False
  else
    if v : (v ≠ vquestion ∧ (∃ N, member_maj N q ∧ vote_rnd2 N p v)) then
      vote_rnd1 n psucc v := True
      in_phase n psucc := True
      in_phase n p := False
    else
      if v : (v ≠ vquestion ∧ coin p v) then
        vote_rnd1 n psucc v := True
        in_phase n psucc := True
        in_phase n p := False
      else
        let v : state_value ← fresh
        assume v ≠ vquestion
        coin p v := True
        vote_rnd1 n psucc v := True
        in_phase n psucc := True
        in_phase n p := False
}

open_isolate protocol

invariant propose N V1 ∧ propose N V2 → V1 = V2
invariant [decision_full_val_inv] decision_full_val N P V → decision_bc N P v1
invariant decision_full_val N P V →
  ∃ Q : set_majority, ∀ N : node, member_maj N Q → propose N V
invariant [decision_full_val_validity] decision_full_val N P V → ∃ N0 : node, propose N0 V
invariant [decision_full_val_agree] decision_full_val N1 P1 V1 ∧ decision_full_val N2 P2 V2 → V1 = V2
invariant [decision_full_noval_inv] decision_full_noval N P → decision_bc N P v0

invariant in_phase N P1 ∧ in_phase N P2 → P1 = P2
invariant vote_rnd1 N P1 V ∧ in_phase N P2 → le P1 P2
invariant vote_rnd2 N P1 V ∧ in_phase N P2 → le P1 P2
invariant vote_rnd2 N P V2 → ∃ V1, vote_rnd1 N P V1
invariant in_phase N P1 → ∃ V1, vote_rnd1 N P1 V1
invariant in_phase N P1 ∧ le P1 P2 ∧ P1 ≠ P2 → ¬ ∃ V1, vote_rnd1 N P2 V1
invariant in_phase N P1 ∧ le P1 P2 ∧ P1 ≠ P2 → ¬ ∃ V1, vote_rnd2 N P2 V1

invariant vote_rnd1 N P V → V ≠ vquestion
invariant vote_rnd1 N P V1 ∧ vote_rnd1 N P V2 → V1 = V2
invariant vote_rnd2 N P V1 ∧ vote_rnd2 N P V2 → V1 = V2
invariant vote_rnd2 N1 P V1 ∧ vote_rnd2 N2 P V2 ∧ V1 ≠ vquestion ∧ V2 ≠ vquestion → V1 = V2
invariant vote_rnd2 N P V ∧ V ≠ vquestion →
  ∃ Q : set_majority, ∀ N : node, member_maj N Q → vote_rnd1 N P V
invariant decision_bc N P1 V ∧ in_phase N P2 → P1 ≠ P2 ∧ le P1 P2
invariant in_phase N P → ¬ ∃ V, decision_bc N P V
invariant decision_bc N1 P1 V1 → V1 ≠ vquestion
invariant decision_bc N P V → ∃ Q : set_f_plus_1, ∀ N : node, member_fp1 N Q → vote_rnd2 N P V

invariant ¬ coin P vquestion
invariant ¬ (coin P v0 ∧ coin P v1)
-- CHECK the following one does not seem to make sense? comment out for now
-- invariant decision_bc N P V ∧ vote_rnd2 N2 P V2 → V2 ≠ vquestion ∨ V2 = V2
invariant ∀ Q, coin P V → ∃ N : node, member_fp1 N Q ∧ vote_rnd2 N P vquestion
invariant decision_bc N P V → ¬ coin P V2

invariant coin P V → ∃ Q : set_majority, ∀ N : node, member_maj N Q → ∃ V, vote_rnd2 N P V
invariant next P P2 ∧ vote_rnd1 N P2 V →
  ∃ Q : set_majority, ∀ N : node, member_maj N Q → ∃ V, vote_rnd2 N P V
invariant next P P2 ∧ vote_rnd1 N P2 V ∧ ¬ coin P v0 ∧ ¬ coin P v1 →
  ∃ (Q : set_majority) (N : node), member_maj N Q ∧ vote_rnd2 N P V

ghost relation state_value_locked (p : phase) (v : state_value) :=
  ∀ N Valt, vote_rnd1 N p Valt → Valt = v

ghost relation strong_state_value_locked (p : phase) (v : state_value) :=
  ∃ N : node, vote_rnd1 N p v ∧ (∀ N Valt, vote_rnd1 N p Valt → Valt = v)   -- CHECK can we just write `state_value_locked` here?

ghost relation members_voted_rnd2 (q : set_majority) (p : phase) :=
  ∀ N, member_maj N q → ∃ V, vote_rnd2 N p V

invariant [vote_rnd1_pred_rnd] vote_rnd1 N1 P2 V1 ∧ next P P2 → ∃ N2, vote_rnd1 N2 P V1

invariant decision_bc N1 P V1 ∧ next P P2 → state_value_locked P2 V1

invariant state_value_locked P V1 ∧ vote_rnd2 N P V2 → V1 = V2 ∨ V2 = vquestion

invariant coin P V →
  ∃ Q : set_majority, ∀ N : node, member_maj N Q → vote_rnd2 N P vquestion

invariant state_value_locked P V → ∀ Q : set_majority, members_voted_rnd2 Q P →
  ∃ N : node, member_maj N Q ∧ vote_rnd2 N P V
invariant state_value_locked P V → ∀ Q : set_majority, members_voted_rnd2 Q P → ¬ coin P V2
invariant state_value_locked P V ∧ next P P2 → state_value_locked P2 V

invariant decision_bc N1 P V1 ∧ next P P2 → ∀ Q : set_majority, members_voted_rnd2 Q P2 →
  ∃ N : node, member_maj N Q ∧ vote_rnd2 N P2 V1
invariant decision_bc N1 P V1 ∧ next P P2 → ¬ ∃ V, coin P2 V

invariant [vl_decision_bc_agree] state_value_locked P V ∧ decision_bc N2 P V2 → V = V2

invariant decision_bc N1 P V1 ∧ next P P2 ∧ decision_bc N2 P2 V2 → V1 = V2

invariant [decision_bc_same_round_agree] decision_bc N1 P V1 ∧ decision_bc N2 P V2 → V1 = V2

invariant (∃ N V, vote_rnd1 N P V) ∧ state_value_locked P V1 ∧ state_value_locked P V2 → V1 = V2

close_isolate

ghost relation started (p : phase) := ∃ N V, vote_rnd1 N p V

ghost relation good (p : phase) :=
  started p ∧
  (∀ P0, lt P0 p → started P0) ∧
  (∀ P0 V0, lt P0 p ∧ started P0 ∧
    ((∃ N, decision_bc N P0 V0) ∨ state_value_locked P0 V0) →
      state_value_locked p V0)

open_isolate wrapper1 with protocol
invariant [good_succ_good] good P ∧ next P P2 ∧ started P2 → good P2
close_isolate

open_isolate wrapper2 with wrapper1
invariant [good_zero] started zero → good zero
close_isolate

open_isolate wrapper3 with wrapper2
invariant [started_pred] started P2 ∧ next P P2 → started P2
close_isolate

open_isolate wrapper4 with protocol
invariant [decision_bc_started] decision_bc N P V2 → started P
close_isolate

open_isolate wrapper5 with protocol
invariant [vote_rnd2_vote_rnd1] vote_rnd2 N P V ∧ V ≠ vquestion → ∃ N2, vote_rnd1 N2 P V
invariant [decision_bc_vote_rnd1] decision_bc N P V → ∃ N2, vote_rnd1 N2 P V
close_isolate

#gen_spec

set_option maxHeartbeats 8000000
set_option auto.smt.timeout 120

set_option sauto.smt.solver "cvc5"
set_option sauto.smt.translator "lean-auto"

#check Lean.Syntax

  @[invProof]
  theorem Rabia.phase_rnd2_good_succ_good :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.good_succ_good node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by
      dsimp only [Rabia.phase_rnd2.ext]
      dsimp only [invSimpLite, inv_28, inv_35, inv_34, inv_8, inv_14, inv_6, inv_9, inv_11, inv_32,
        inv_10, decision_full_val_validity, inv_37, inv_31, inv_16, vote_rnd1_pred_rnd,
        decision_full_val_agree, inv_19, inv_33, good_succ_good, inv_26, inv_7, inv_15, inv_23,
        inv_39, inv_36, inv_17, inv_22, inv_20, inv_2, decision_full_val_inv, inv_12,
        decision_bc_same_round_agree, inv_0, inv_13, decision_full_noval_inv, inv_41, inv_21,
        inv_24, inv_18, inv_27, inv_30, inv_25, vl_decision_bc_agree]
      intros st; sdestruct_hyps
      first
      | intro ass_ inv_;
        intro (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value);
        unhygienic cases st'; revert ass_ inv_; dsimp only
      | try dsimp only
        try simp only [exists_imp, and_imp]
        unhygienic intros
        clear_invariants
        try simp only [ifSimp]
      split_ifs with exists_imp, and_imp
      · sauto_all
      · sauto_all
      · sauto_all
      · sauto_all



#exit

#time @[invProof]
  theorem init_inv_0 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_0 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_decision_full_val_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.decision_full_val_inv node node_dec node_ne set_majority set_majority_dec
                set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                state_value_dec state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_2 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_2 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_decision_full_val_validity :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.decision_full_val_validity node node_dec node_ne set_majority set_majority_dec
                set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                state_value_dec state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_decision_full_val_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.decision_full_val_agree node node_dec node_ne set_majority set_majority_dec
                set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                state_value_dec state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_decision_full_noval_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.decision_full_noval_inv node node_dec node_ne set_majority set_majority_dec
                set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                state_value_dec state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_6 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_6 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_7 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_7 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_8 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_8 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_9 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_9 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_10 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_10 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_11 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_11 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_12 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_12 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_13 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_13 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_14 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_14 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_15 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_15 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_16 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_16 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_17 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_17 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_18 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_18 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_19 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_19 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_20 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_20 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_21 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_21 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_22 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_22 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_23 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_23 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_24 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_24 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_25 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_25 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_26 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_26 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_27 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_27 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_28 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_28 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_vote_rnd1_pred_rnd :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.vote_rnd1_pred_rnd node node_dec node_ne set_majority set_majority_dec
                set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                state_value_dec state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_30 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_30 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_31 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_31 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_32 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_32 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_33 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_33 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_34 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_34 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_35 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_35 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_36 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_36 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_37 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_37 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_vl_decision_bc_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.vl_decision_bc_agree node node_dec node_ne set_majority set_majority_dec
                set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                state_value_dec state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_39 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_39 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_decision_bc_same_round_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.decision_bc_same_round_agree node node_dec node_ne set_majority set_majority_dec
                set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                state_value_dec state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_inv_41 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.inv_41 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_good_succ_good :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.good_succ_good node node_dec node_ne set_majority set_majority_dec
                set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                state_value_dec state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_good_zero :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.good_zero node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_started_pred :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.started_pred node node_dec node_ne set_majority set_majority_dec set_majority_ne
                set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_decision_bc_started :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.decision_bc_started node node_dec node_ne set_majority set_majority_dec
                set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                state_value_dec state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_vote_rnd2_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.vote_rnd2_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                state_value_dec state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem init_decision_bc_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).assumptions
            st →
          (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                  set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                  proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                  tv).init
              st →
            (@Rabia.decision_bc_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                state_value_dec state_value_ne tv)
              st :=
    by (unhygienic intros); solve_clause[initSimp]

  @[invProof]
  theorem Rabia.initial_proposal_inv_0 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_0 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_0

  @[invProof]
  theorem Rabia.initial_proposal_decision_full_val_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_inv node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.decision_full_val_inv

  @[invProof]
  theorem Rabia.initial_proposal_inv_2 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_2 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_2

  @[invProof]
  theorem Rabia.initial_proposal_decision_full_val_validity :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_validity node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.decision_full_val_validity

  @[invProof]
  theorem Rabia.initial_proposal_decision_full_val_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_agree node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.decision_full_val_agree

  @[invProof]
  theorem Rabia.initial_proposal_decision_full_noval_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_noval_inv node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.decision_full_noval_inv

  @[invProof]
  theorem Rabia.initial_proposal_inv_6 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_6 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_6

  @[invProof]
  theorem Rabia.initial_proposal_inv_7 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_7 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_7

  @[invProof]
  theorem Rabia.initial_proposal_inv_8 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_8 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_8

  @[invProof]
  theorem Rabia.initial_proposal_inv_9 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_9 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_9

  @[invProof]
  theorem Rabia.initial_proposal_inv_10 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_10 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_10

  @[invProof]
  theorem Rabia.initial_proposal_inv_11 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_11 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_11

  @[invProof]
  theorem Rabia.initial_proposal_inv_12 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_12 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_12

  @[invProof]
  theorem Rabia.initial_proposal_inv_13 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_13 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_13

  @[invProof]
  theorem Rabia.initial_proposal_inv_14 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_14 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_14

  @[invProof]
  theorem Rabia.initial_proposal_inv_15 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_15 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_15

  @[invProof]
  theorem Rabia.initial_proposal_inv_16 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_16 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_16

  @[invProof]
  theorem Rabia.initial_proposal_inv_17 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_17 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_17

  @[invProof]
  theorem Rabia.initial_proposal_inv_18 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_18 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_18

  @[invProof]
  theorem Rabia.initial_proposal_inv_19 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_19 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_19

  @[invProof]
  theorem Rabia.initial_proposal_inv_20 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_20 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_20

  @[invProof]
  theorem Rabia.initial_proposal_inv_21 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_21 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_21

  @[invProof]
  theorem Rabia.initial_proposal_inv_22 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_22 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_22

  @[invProof]
  theorem Rabia.initial_proposal_inv_23 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_23 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_23

  @[invProof]
  theorem Rabia.initial_proposal_inv_24 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_24 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_24

  @[invProof]
  theorem Rabia.initial_proposal_inv_25 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_25 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_25

  @[invProof]
  theorem Rabia.initial_proposal_inv_26 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_26 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_26

  @[invProof]
  theorem Rabia.initial_proposal_inv_27 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_27 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_27

  @[invProof]
  theorem Rabia.initial_proposal_inv_28 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_28 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_28

  @[invProof]
  theorem Rabia.initial_proposal_vote_rnd1_pred_rnd :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vote_rnd1_pred_rnd node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.vote_rnd1_pred_rnd

  @[invProof]
  theorem Rabia.initial_proposal_inv_30 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_30 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_30

  @[invProof]
  theorem Rabia.initial_proposal_inv_31 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_31 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_31

  @[invProof]
  theorem Rabia.initial_proposal_inv_32 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_32 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_32

  @[invProof]
  theorem Rabia.initial_proposal_inv_33 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_33 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_33

  @[invProof]
  theorem Rabia.initial_proposal_inv_34 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_34 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_34

  @[invProof]
  theorem Rabia.initial_proposal_inv_35 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_35 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_35

  @[invProof]
  theorem Rabia.initial_proposal_inv_36 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_36 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_36

  @[invProof]
  theorem Rabia.initial_proposal_inv_37 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_37 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_37

  @[invProof]
  theorem Rabia.initial_proposal_vl_decision_bc_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vl_decision_bc_agree node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.vl_decision_bc_agree

  @[invProof]
  theorem Rabia.initial_proposal_inv_39 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_39 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_39

  @[invProof]
  theorem Rabia.initial_proposal_decision_bc_same_round_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_same_round_agree node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.decision_bc_same_round_agree

  @[invProof]
  theorem Rabia.initial_proposal_inv_41 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_41 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.inv_41

  @[invProof]
  theorem Rabia.initial_proposal_good_succ_good :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.good_succ_good node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.good_succ_good

  @[invProof]
  theorem Rabia.initial_proposal_good_zero :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.good_zero node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.good_zero

  @[invProof]
  theorem Rabia.initial_proposal_started_pred :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.started_pred node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.started_pred

  @[invProof]
  theorem Rabia.initial_proposal_decision_bc_started :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_started node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.decision_bc_started

  @[invProof]
  theorem Rabia.initial_proposal_vote_rnd2_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vote_rnd2_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.vote_rnd2_vote_rnd1

  @[invProof]
  theorem Rabia.initial_proposal_decision_bc_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_proposal.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_proposal.ext Rabia.decision_bc_vote_rnd1

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_0 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_0 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_0

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_decision_full_val_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_inv node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.decision_full_val_inv

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_2 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_2 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_2

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_decision_full_val_validity :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_validity node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.decision_full_val_validity

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_decision_full_val_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_agree node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.decision_full_val_agree

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_decision_full_noval_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_noval_inv node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.decision_full_noval_inv

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_6 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_6 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_6

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_7 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_7 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_7

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_8 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_8 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_8

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_9 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_9 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_9

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_10 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_10 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_10

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_11 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_11 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_11

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_12 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_12 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_12

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_13 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_13 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_13

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_14 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_14 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_14

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_15 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_15 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_15

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_16 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_16 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_16

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_17 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_17 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_17

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_18 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_18 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_18

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_19 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_19 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_19

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_20 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_20 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_20

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_21 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_21 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_21

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_22 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_22 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_22

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_23 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_23 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_23

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_24 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_24 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_24

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_25 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_25 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_25

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_26 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_26 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_26

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_27 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_27 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_27

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_28 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_28 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_28

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_vote_rnd1_pred_rnd :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vote_rnd1_pred_rnd node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.vote_rnd1_pred_rnd

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_30 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_30 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_30

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_31 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_31 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_31

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_32 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_32 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_32

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_33 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_33 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_33

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_34 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_34 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_34

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_35 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_35 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_35

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_36 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_36 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_36

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_37 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_37 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_37

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_vl_decision_bc_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vl_decision_bc_agree node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.vl_decision_bc_agree

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_39 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_39 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_39

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_decision_bc_same_round_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_same_round_agree node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.decision_bc_same_round_agree

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_inv_41 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_41 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.inv_41

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_good_succ_good :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.good_succ_good node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.good_succ_good

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_good_zero :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.good_zero node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.good_zero

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_started_pred :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.started_pred node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.started_pred

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_decision_bc_started :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_started node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.decision_bc_started

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_vote_rnd2_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vote_rnd2_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.vote_rnd2_vote_rnd1

  @[invProof]
  theorem Rabia.decide_bc_decide_full_val_decision_bc_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_val.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_val.ext Rabia.decision_bc_vote_rnd1

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_0 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_0 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_0

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_decision_full_val_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_inv node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.decision_full_val_inv

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_2 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_2 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_2

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_decision_full_val_validity :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_validity node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.decision_full_val_validity

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_decision_full_val_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_agree node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.decision_full_val_agree

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_decision_full_noval_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_noval_inv node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.decision_full_noval_inv

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_6 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_6 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_6

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_7 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_7 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_7

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_8 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_8 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_8

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_9 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_9 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_9

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_10 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_10 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_10

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_11 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_11 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_11

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_12 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_12 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_12

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_13 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_13 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_13

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_14 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_14 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_14

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_15 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_15 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_15

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_16 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_16 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_16

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_17 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_17 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_17

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_18 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_18 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_18

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_19 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_19 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_19

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_20 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_20 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_20

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_21 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_21 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_21

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_22 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_22 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_22

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_23 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_23 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_23

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_24 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_24 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_24

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_25 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_25 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_25

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_26 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_26 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_26

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_27 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_27 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_27

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_28 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_28 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_28

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_vote_rnd1_pred_rnd :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vote_rnd1_pred_rnd node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.vote_rnd1_pred_rnd

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_30 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_30 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_30

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_31 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_31 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_31

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_32 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_32 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_32

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_33 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_33 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_33

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_34 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_34 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_34

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_35 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_35 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_35

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_36 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_36 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_36

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_37 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_37 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_37

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_vl_decision_bc_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vl_decision_bc_agree node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.vl_decision_bc_agree

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_39 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_39 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_39

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_decision_bc_same_round_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_same_round_agree node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.decision_bc_same_round_agree

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_inv_41 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_41 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.inv_41

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_good_succ_good :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.good_succ_good node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.good_succ_good

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_good_zero :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.good_zero node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.good_zero

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_started_pred :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.started_pred node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.started_pred

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_decision_bc_started :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_started node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.decision_bc_started

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_vote_rnd2_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vote_rnd2_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.vote_rnd2_vote_rnd1

  @[invProof]
  theorem Rabia.decide_bc_decide_full_noval_decision_bc_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.decide_bc_decide_full_noval.ext node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.decide_bc_decide_full_noval.ext Rabia.decision_bc_vote_rnd1

  @[invProof]
  theorem Rabia.initial_vote1_inv_0 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_0 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_0

  @[invProof]
  theorem Rabia.initial_vote1_decision_full_val_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_inv node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.decision_full_val_inv

  @[invProof]
  theorem Rabia.initial_vote1_inv_2 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_2 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_2

  @[invProof]
  theorem Rabia.initial_vote1_decision_full_val_validity :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_validity node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.decision_full_val_validity

  @[invProof]
  theorem Rabia.initial_vote1_decision_full_val_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_agree node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.decision_full_val_agree

  @[invProof]
  theorem Rabia.initial_vote1_decision_full_noval_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_noval_inv node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.decision_full_noval_inv

  @[invProof]
  theorem Rabia.initial_vote1_inv_6 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_6 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_6

  @[invProof]
  theorem Rabia.initial_vote1_inv_7 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_7 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_7

  @[invProof]
  theorem Rabia.initial_vote1_inv_8 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_8 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_8

  @[invProof]
  theorem Rabia.initial_vote1_inv_9 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_9 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_9

  @[invProof]
  theorem Rabia.initial_vote1_inv_10 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_10 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_10

  @[invProof]
  theorem Rabia.initial_vote1_inv_11 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_11 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_11

  @[invProof]
  theorem Rabia.initial_vote1_inv_12 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_12 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_12

  @[invProof]
  theorem Rabia.initial_vote1_inv_13 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_13 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_13

  @[invProof]
  theorem Rabia.initial_vote1_inv_14 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_14 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_14

  @[invProof]
  theorem Rabia.initial_vote1_inv_15 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_15 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_15

  @[invProof]
  theorem Rabia.initial_vote1_inv_16 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_16 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_16

  @[invProof]
  theorem Rabia.initial_vote1_inv_17 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_17 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_17

  @[invProof]
  theorem Rabia.initial_vote1_inv_18 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_18 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_18

  @[invProof]
  theorem Rabia.initial_vote1_inv_19 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_19 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_19

  @[invProof]
  theorem Rabia.initial_vote1_inv_20 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_20 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_20

  @[invProof]
  theorem Rabia.initial_vote1_inv_21 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_21 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_21

  @[invProof]
  theorem Rabia.initial_vote1_inv_22 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_22 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_22

  @[invProof]
  theorem Rabia.initial_vote1_inv_23 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_23 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_23

  @[invProof]
  theorem Rabia.initial_vote1_inv_24 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_24 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_24

  @[invProof]
  theorem Rabia.initial_vote1_inv_25 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_25 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_25

  @[invProof]
  theorem Rabia.initial_vote1_inv_26 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_26 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_26

  @[invProof]
  theorem Rabia.initial_vote1_inv_27 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_27 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_27

  @[invProof]
  theorem Rabia.initial_vote1_inv_28 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_28 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_28

  @[invProof]
  theorem Rabia.initial_vote1_vote_rnd1_pred_rnd :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vote_rnd1_pred_rnd node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.vote_rnd1_pred_rnd

  @[invProof]
  theorem Rabia.initial_vote1_inv_30 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_30 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_30

  @[invProof]
  theorem Rabia.initial_vote1_inv_31 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_31 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_31

  @[invProof]
  theorem Rabia.initial_vote1_inv_32 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_32 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_32

  @[invProof]
  theorem Rabia.initial_vote1_inv_33 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_33 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_33

  @[invProof]
  theorem Rabia.initial_vote1_inv_34 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_34 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_34

  @[invProof]
  theorem Rabia.initial_vote1_inv_35 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_35 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_35

  @[invProof]
  theorem Rabia.initial_vote1_inv_36 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_36 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_36

  @[invProof]
  theorem Rabia.initial_vote1_inv_37 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_37 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_37

  @[invProof]
  theorem Rabia.initial_vote1_vl_decision_bc_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vl_decision_bc_agree node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.vl_decision_bc_agree

  @[invProof]
  theorem Rabia.initial_vote1_inv_39 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_39 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_39

  @[invProof]
  theorem Rabia.initial_vote1_decision_bc_same_round_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_same_round_agree node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.decision_bc_same_round_agree

  @[invProof]
  theorem Rabia.initial_vote1_inv_41 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_41 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.inv_41

  @[invProof]
  theorem Rabia.initial_vote1_good_succ_good :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.good_succ_good node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.good_succ_good

  @[invProof]
  theorem Rabia.initial_vote1_good_zero :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.good_zero node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.good_zero

  @[invProof]
  theorem Rabia.initial_vote1_started_pred :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.started_pred node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.started_pred

  @[invProof]
  theorem Rabia.initial_vote1_decision_bc_started :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_started node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.decision_bc_started

  @[invProof]
  theorem Rabia.initial_vote1_vote_rnd2_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vote_rnd2_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.vote_rnd2_vote_rnd1

  @[invProof]
  theorem Rabia.initial_vote1_decision_bc_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.initial_vote1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.initial_vote1.ext Rabia.decision_bc_vote_rnd1

  @[invProof]
  theorem Rabia.phase_rnd1_inv_0 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_0 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_0

  @[invProof]
  theorem Rabia.phase_rnd1_decision_full_val_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_inv node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.decision_full_val_inv

  @[invProof]
  theorem Rabia.phase_rnd1_inv_2 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_2 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_2

  @[invProof]
  theorem Rabia.phase_rnd1_decision_full_val_validity :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_validity node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.decision_full_val_validity

  @[invProof]
  theorem Rabia.phase_rnd1_decision_full_val_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_agree node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.decision_full_val_agree

  @[invProof]
  theorem Rabia.phase_rnd1_decision_full_noval_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_noval_inv node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.decision_full_noval_inv

  @[invProof]
  theorem Rabia.phase_rnd1_inv_6 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_6 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_6

  @[invProof]
  theorem Rabia.phase_rnd1_inv_7 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_7 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_7

  @[invProof]
  theorem Rabia.phase_rnd1_inv_8 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_8 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_8

  @[invProof]
  theorem Rabia.phase_rnd1_inv_9 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_9 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_9

  @[invProof]
  theorem Rabia.phase_rnd1_inv_10 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_10 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_10

  @[invProof]
  theorem Rabia.phase_rnd1_inv_11 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_11 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_11

  @[invProof]
  theorem Rabia.phase_rnd1_inv_12 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_12 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_12

  @[invProof]
  theorem Rabia.phase_rnd1_inv_13 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_13 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_13

  @[invProof]
  theorem Rabia.phase_rnd1_inv_14 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_14 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_14

  @[invProof]
  theorem Rabia.phase_rnd1_inv_15 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_15 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_15

  @[invProof]
  theorem Rabia.phase_rnd1_inv_16 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_16 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_16

  @[invProof]
  theorem Rabia.phase_rnd1_inv_17 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_17 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_17

  @[invProof]
  theorem Rabia.phase_rnd1_inv_18 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_18 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_18

  @[invProof]
  theorem Rabia.phase_rnd1_inv_19 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_19 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_19

  @[invProof]
  theorem Rabia.phase_rnd1_inv_20 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_20 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_20

  @[invProof]
  theorem Rabia.phase_rnd1_inv_21 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_21 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_21

  @[invProof]
  theorem Rabia.phase_rnd1_inv_22 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_22 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_22

  @[invProof]
  theorem Rabia.phase_rnd1_inv_23 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_23 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_23

  @[invProof]
  theorem Rabia.phase_rnd1_inv_24 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_24 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_24

  @[invProof]
  theorem Rabia.phase_rnd1_inv_25 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_25 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_25

  @[invProof]
  theorem Rabia.phase_rnd1_inv_26 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_26 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_26

  @[invProof]
  theorem Rabia.phase_rnd1_inv_27 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_27 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_27

  @[invProof]
  theorem Rabia.phase_rnd1_inv_28 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_28 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_28

  @[invProof]
  theorem Rabia.phase_rnd1_vote_rnd1_pred_rnd :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vote_rnd1_pred_rnd node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.vote_rnd1_pred_rnd

  @[invProof]
  theorem Rabia.phase_rnd1_inv_30 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_30 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_30

  @[invProof]
  theorem Rabia.phase_rnd1_inv_31 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_31 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_31

  @[invProof]
  theorem Rabia.phase_rnd1_inv_32 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_32 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_32

  @[invProof]
  theorem Rabia.phase_rnd1_inv_33 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_33 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_33

  @[invProof]
  theorem Rabia.phase_rnd1_inv_34 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_34 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_34

  @[invProof]
  theorem Rabia.phase_rnd1_inv_35 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_35 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_35

  @[invProof]
  theorem Rabia.phase_rnd1_inv_36 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_36 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_36

  @[invProof]
  theorem Rabia.phase_rnd1_inv_37 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_37 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_37

  @[invProof]
  theorem Rabia.phase_rnd1_vl_decision_bc_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vl_decision_bc_agree node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.vl_decision_bc_agree

  @[invProof]
  theorem Rabia.phase_rnd1_inv_39 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_39 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_39

  @[invProof]
  theorem Rabia.phase_rnd1_decision_bc_same_round_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_same_round_agree node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.decision_bc_same_round_agree

  @[invProof]
  theorem Rabia.phase_rnd1_inv_41 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_41 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.inv_41

  @[invProof]
  theorem Rabia.phase_rnd1_good_succ_good :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.good_succ_good node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.good_succ_good

  @[invProof]
  theorem Rabia.phase_rnd1_good_zero :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.good_zero node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.good_zero

  @[invProof]
  theorem Rabia.phase_rnd1_started_pred :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.started_pred node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.started_pred

  @[invProof]
  theorem Rabia.phase_rnd1_decision_bc_started :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_started node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.decision_bc_started

  @[invProof]
  theorem Rabia.phase_rnd1_vote_rnd2_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vote_rnd2_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.vote_rnd2_vote_rnd1

  @[invProof]
  theorem Rabia.phase_rnd1_decision_bc_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd1.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd1.ext Rabia.decision_bc_vote_rnd1

  @[invProof]
  theorem Rabia.phase_rnd2_inv_0 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_0 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_0

  @[invProof]
  theorem Rabia.phase_rnd2_decision_full_val_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_inv node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.decision_full_val_inv

  @[invProof]
  theorem Rabia.phase_rnd2_inv_2 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_2 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_2

  @[invProof]
  theorem Rabia.phase_rnd2_decision_full_val_validity :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_validity node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.decision_full_val_validity

  @[invProof]
  theorem Rabia.phase_rnd2_decision_full_val_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_val_agree node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.decision_full_val_agree

  @[invProof]
  theorem Rabia.phase_rnd2_decision_full_noval_inv :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_full_noval_inv node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.decision_full_noval_inv

  @[invProof]
  theorem Rabia.phase_rnd2_inv_6 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_6 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_6

  @[invProof]
  theorem Rabia.phase_rnd2_inv_7 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_7 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_7

  @[invProof]
  theorem Rabia.phase_rnd2_inv_8 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_8 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_8

  @[invProof]
  theorem Rabia.phase_rnd2_inv_9 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_9 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_9

  @[invProof]
  theorem Rabia.phase_rnd2_inv_10 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_10 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_10

  @[invProof]
  theorem Rabia.phase_rnd2_inv_11 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_11 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_11

  @[invProof]
  theorem Rabia.phase_rnd2_inv_12 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_12 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_12

  @[invProof]
  theorem Rabia.phase_rnd2_inv_13 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_13 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_13

  @[invProof]
  theorem Rabia.phase_rnd2_inv_14 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_14 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_14

  @[invProof]
  theorem Rabia.phase_rnd2_inv_15 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_15 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_15

  @[invProof]
  theorem Rabia.phase_rnd2_inv_16 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_16 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_16

  @[invProof]
  theorem Rabia.phase_rnd2_inv_17 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_17 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_17

  @[invProof]
  theorem Rabia.phase_rnd2_inv_18 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_18 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_18

  @[invProof]
  theorem Rabia.phase_rnd2_inv_19 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_19 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_19

  @[invProof]
  theorem Rabia.phase_rnd2_inv_20 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_20 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_20

  @[invProof]
  theorem Rabia.phase_rnd2_inv_21 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_21 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_21

  @[invProof]
  theorem Rabia.phase_rnd2_inv_22 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_22 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_22

  @[invProof]
  theorem Rabia.phase_rnd2_inv_23 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_23 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_23

  @[invProof]
  theorem Rabia.phase_rnd2_inv_24 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_24 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_24

  @[invProof]
  theorem Rabia.phase_rnd2_inv_25 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_25 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_25

  @[invProof]
  theorem Rabia.phase_rnd2_inv_26 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_26 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_26

  @[invProof]
  theorem Rabia.phase_rnd2_inv_27 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_27 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_27

  @[invProof]
  theorem Rabia.phase_rnd2_inv_28 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_28 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_28

  @[invProof]
  theorem Rabia.phase_rnd2_vote_rnd1_pred_rnd :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vote_rnd1_pred_rnd node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.vote_rnd1_pred_rnd

  @[invProof]
  theorem Rabia.phase_rnd2_inv_30 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_30 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_30

  @[invProof]
  theorem Rabia.phase_rnd2_inv_31 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_31 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_31

  @[invProof]
  theorem Rabia.phase_rnd2_inv_32 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_32 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_32

  @[invProof]
  theorem Rabia.phase_rnd2_inv_33 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_33 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_33

  @[invProof]
  theorem Rabia.phase_rnd2_inv_34 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_34 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_34

  @[invProof]
  theorem Rabia.phase_rnd2_inv_35 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_35 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_35

  @[invProof]
  theorem Rabia.phase_rnd2_inv_36 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_36 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_36

  @[invProof]
  theorem Rabia.phase_rnd2_inv_37 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_37 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_37

  @[invProof]
  theorem Rabia.phase_rnd2_vl_decision_bc_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vl_decision_bc_agree node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.vl_decision_bc_agree

  @[invProof]
  theorem Rabia.phase_rnd2_inv_39 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_39 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_39

  @[invProof]
  theorem Rabia.phase_rnd2_decision_bc_same_round_agree :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_same_round_agree node node_dec node_ne set_majority
                  set_majority_dec set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg
                  phase phase_dec phase_ne tot proposal_value proposal_value_dec proposal_value_ne
                  state_value state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.decision_bc_same_round_agree

  @[invProof]
  theorem Rabia.phase_rnd2_inv_41 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.inv_41 node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.inv_41


  @[invProof]
  theorem Rabia.phase_rnd2_good_zero :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.good_zero node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.good_zero

  @[invProof]
  theorem Rabia.phase_rnd2_started_pred :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.started_pred node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.started_pred

  @[invProof]
  theorem Rabia.phase_rnd2_decision_bc_started :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_started node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.decision_bc_started

  @[invProof]
  theorem Rabia.phase_rnd2_vote_rnd2_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.vote_rnd2_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.vote_rnd2_vote_rnd1

  @[invProof]
  theorem Rabia.phase_rnd2_decision_bc_vote_rnd1 :
      ∀ (st : @State node set_majority set_f_plus_1 phase proposal_value state_value),
        forall?,(@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                  set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                  proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                  state_value_ne tv).assumptions
              st →
            (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne
                    set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot
                    proposal_value proposal_value_dec proposal_value_ne state_value state_value_dec
                    state_value_ne tv).inv
                st →
              (@Rabia.phase_rnd2.ext node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv)
                st
                fun _
                  (st' : @State node set_majority set_f_plus_1 phase proposal_value state_value) =>
                @Rabia.decision_bc_vote_rnd1 node node_dec node_ne set_majority set_majority_dec
                  set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                  phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                  state_value_dec state_value_ne tv st' :=
    by solve_wlp_clause Rabia.phase_rnd2.ext Rabia.decision_bc_vote_rnd1



#time #recover_invariants_in_tr

prove_inv_inductive by {
  constructor
  . intro st has hinit
    sdestruct_goal <;> already_proven_init
  · intro st st' has hinv hnext
    sts_induction <;> sdestruct_goal <;> already_proven_next_tr
}

end Rabia
