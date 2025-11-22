import Veil

-- import Veil.DSL.Check.InvariantManipulation

-- adapted from [weak_mvc.ivy](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/ivy/weak_mvc.ivy)

-- axioms from the Ivy spec
class Rabia.Background (node set_majority set_f_plus_1 : outParam Type) where
  member_maj : node → set_majority → Prop
  member_fp1 : node → set_f_plus_1 → Prop

  ax0 : ∀ (Q1 Q2 : set_majority), ∃ (N : node), member_maj N Q1 ∧ member_maj N Q2
  ax1 : ∀ (Q1 : set_majority) (Q2 : set_f_plus_1), ∃ (N : node), member_maj N Q1 ∧ member_fp1 N Q2
veil module Rabia


-- this enables `#recover_invariants_in_tr` to work
-- everything after `#check_invariants` is not part of evaluation as such, but we leave it for completeness
-- set_option veil.gen_sound true
-- set_option synthInstance.maxSize 8192

type node
type set_majority
type set_f_plus_1
instantiate bg : Background node set_majority set_f_plus_1

type phase
instantiate tot : TotalOrderWithMinimum phase

relation in_phase : node → phase → Bool

type proposal_value
enum state_value = { v0, v1, vquestion }

open TotalOrderWithMinimum Background

relation propose : node → proposal_value → Bool
relation vote_rnd1 : node → phase → state_value → Bool
relation vote_rnd2 : node → phase → state_value → Bool

relation decision_bc : node → phase → state_value → Bool
relation decision_full_val : node → phase → proposal_value → Bool
relation decision_full_noval : node → phase → Bool
relation coin : phase → state_value → Bool

#gen_state

after_init {
  in_phase N P := false;
  decision_bc N P V := false;
  decision_full_val N P V := false;
  decision_full_noval N P := false;
  propose N V := false;
  vote_rnd1 N P V := false;
  vote_rnd2 N P V := false;
  coin P V := false
}

action initial_proposal {
  let n : node ← pick
  let v : proposal_value ← pick
  assume ¬ ∃ V : proposal_value, propose n V
  assume ∀ P, ¬ ∃ V : state_value, vote_rnd1 n P V
  assume ∀ P, ¬ ∃ V : state_value, vote_rnd2 n P V
  assume ∀ P, ¬ ∃ V : state_value, decision_bc n P V
  assume ∀ P, ¬ in_phase n P
  propose n v := true
}

action decide_bc_decide_full_val {
  let n : node ← pick
  let p : phase ← pick
  let q : set_majority ← pick
  assume decision_bc n p v1
  if v : (∀ (N : node), member_maj N q → propose N v) then
    decision_full_val n p v := true
}

action decide_bc_decide_full_noval {
  let n : node ← pick
  let p : phase ← pick
  assume decision_bc n p v0
  decision_full_noval n p := true
}

action initial_vote1 {
  let n : node ← pick
  let q : set_majority ← pick
  assume ∃ V : proposal_value, propose n V
  assume ∀ P, ¬ ∃ V : state_value, vote_rnd1 n P V
  assume ∀ P, ¬ ∃ V : state_value, vote_rnd2 n P V
  assume ∀ P, ¬ ∃ V : state_value, decision_bc n P V
  assume ∀ P, ¬ in_phase n P

  if v : (∀ (N : node), member_maj N q → propose N v) then
    vote_rnd1 n zero v1 := true
    in_phase n zero := true
  else
    vote_rnd1 n zero v0 := true
    in_phase n zero := true
}

action phase_rnd1 {
  let n : node ← pick
  let p : phase ← pick
  let q : set_majority ← pick
  assume in_phase n p
  assume ¬ ∃ V : state_value, vote_rnd2 n p V
  assume ∀ (N : node), member_maj N q → ∃ V, vote_rnd1 N p V

  if v : (∀ (N : node), member_maj N q → vote_rnd1 N p v) then
    vote_rnd2 n p v := true
  else
    vote_rnd2 n p vquestion := true
}

action phase_rnd2 {
  let n : node ← pick
  let p : phase ← pick
  let psucc : phase ← pick
  let q : set_majority ← pick
  assume in_phase n p
  assume ∃ V : state_value, vote_rnd2 n p V
  assume ∀ (N : node), member_maj N q → ∃ V, vote_rnd2 N p V
  assume next p psucc

  if v : (v ≠ vquestion ∧
      (∃ N0 Q, member_fp1 N0 Q ∧ (∀ N, member_fp1 N Q → member_maj N q ∧ vote_rnd2 N p v)))
  then
    decision_bc n p v := true
    vote_rnd1 n psucc v := true
    in_phase n psucc := true
    in_phase n p := false
  else
    if v : (v ≠ vquestion ∧ (∃ N, member_maj N q ∧ vote_rnd2 N p v)) then
      vote_rnd1 n psucc v := true
      in_phase n psucc := true
      in_phase n p := false
    else
      if v : (v ≠ vquestion ∧ coin p v) then
        vote_rnd1 n psucc v := true
        in_phase n psucc := true
        in_phase n p := false
      else
        let v : state_value ← pick
        assume v ≠ vquestion
        coin p v := true
        vote_rnd1 n psucc v := true
        in_phase n psucc := true
        in_phase n p := false
}

-- NOTE: the following `isolate`s correspond to the `isolate`s in the Ivy spec
-- open_isolate protocol

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

-- close_isolate

ghost relation started (p : phase) := ∃ N V, vote_rnd1 N p V

ghost relation good (p : phase) :=
  started p ∧
  (∀ P0, lt P0 p → started P0) ∧
  (∀ P0 V0, lt P0 p ∧ started P0 ∧
    ((∃ N, decision_bc N P0 V0) ∨ state_value_locked P0 V0) →
      state_value_locked p V0)

-- open_isolate wrapper1 with protocol
invariant [good_succ_good] good P ∧ next P P2 ∧ started P2 → good P2
-- close_isolate

-- open_isolate wrapper2 with wrapper1
invariant [good_zero] started zero → good zero
-- close_isolate

-- open_isolate wrapper3 with wrapper2
invariant [started_pred] started P2 ∧ next P P2 → started P
-- close_isolate

-- open_isolate wrapper4 with protocol
invariant [decision_bc_started] decision_bc N P V2 → started P
-- close_isolate

-- open_isolate wrapper5 with protocol
invariant [vote_rnd2_vote_rnd1] vote_rnd2 N P V ∧ V ≠ vquestion → ∃ N2, vote_rnd1 N2 P V
invariant [decision_bc_vote_rnd1] decision_bc N P V → ∃ N2, vote_rnd1 N2 P V
-- close_isolate

#gen_spec

set_option maxHeartbeats 8000000
-- set_option veil.smt.timeout 120

-- #time #check_isolate protocol

end Rabia
