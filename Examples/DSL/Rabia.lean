import Veil.State
import Veil.TransitionSystem
import Veil.Tactic
import Veil.DSL
import Examples.DSL.Std

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

namespace Rabia
open Classical

type node
type set_majority
type set_f_plus_1

-- NOTE: might also be made as typeclass
immutable relation member_maj : node → set_majority → Prop
immutable relation member_fp1 : node → set_f_plus_1 → Prop

type phase
instantiate tot : TotalOrderWithMinimum phase

relation in_phase : node → phase → Prop

type proposal_value
type state_value
-- poor man's enum type
instantiate tv : ThreeValuedType state_value

open ThreeValuedType TotalOrderWithMinimum

relation propose : node → proposal_value → Prop
relation vote_rnd1 : node → phase → state_value → Prop
relation vote_rnd2 : node → phase → state_value → Prop

relation decision_bc : node → phase → state_value → Prop
relation decision_full_val : node → phase → proposal_value → Prop
relation decision_full_noval : node → phase → Prop
relation coin : phase → state_value → Prop

#gen_state

assumption ∀ (Q1 Q2 : set_majority), ∃ (N : node), member_maj N Q1 ∧ member_maj N Q2
assumption ∀ (Q1 : set_majority) (Q2 : set_f_plus_1), ∃ (N : node), member_maj N Q1 ∧ member_fp1 N Q2

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
        require v ≠ vquestion
        coin p v := True
        vote_rnd1 n psucc v := True
        in_phase n psucc := True
        in_phase n p := False
}

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

-- CHECK is the following translation correct?

ghost relation started (p : phase) := ∃ N V, vote_rnd1 N p V

ghost relation good (p : phase) :=
  started p ∧
  (∀ P0, lt P0 p → started P0) ∧
  (∀ P0 V0, lt P0 p ∧ started P0 ∧
    (((∃ N, decision_bc N P0 V0) ∨ state_value_locked P0 V0) →
      state_value_locked p V0))

-- safety?
safety [good_succ_good] good P ∧ next P P2 ∧ started P2 → good P2
safety [good_zero] started zero → good zero
safety [started_pred] started P2 ∧ next P P2 → started P2
safety [decision_bc_started] decision_bc N P V2 → started P
safety [vote_rnd2_vote_rnd1] vote_rnd2 N P V ∧ V ≠ vquestion → ∃ N2, vote_rnd1 N2 P V
safety [decision_bc_vote_rnd1] decision_bc N P V → ∃ N2, vote_rnd1 N2 P V

#gen_spec

set_option maxHeartbeats 8000000
set_option auto.smt.timeout 15

#check_invariants

end Rabia
