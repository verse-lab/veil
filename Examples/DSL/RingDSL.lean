import LeanSts.State
import LeanSts.TransitionSystem
import LeanSts.Tactic
import LeanSts.DSL
-- import Mathlib.Tactic


-- https://github.com/aman-goel/ivybench/blob/5db7eccb5c3bc2dd14dfb58eddb859b036d699f5/ex/ivy/ring.ivy

section Ring

class TotalOrder (t : Type) :=
  -- relation: total order
  le (x y : t) : Prop
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x

class Between (node : Type) :=
  -- relation: btw represents a ring
  -- read: y is between x and z
  btw (x y z : node) : Prop
  -- axioms
  btw_ring    (x y z : node) : btw x y z → btw y z x
  btw_trans (w x y z : node) : btw w x y → btw w y z → btw w x z
  btw_side    (w x y : node) : btw w x y → ¬ btw w y x
  btw_total   (w x y : node) : btw w x y ∨ btw w y x ∨ w = x ∨ w = y ∨ x = y

type node
instantiate dec : DecidableEq node
instantiate tot : TotalOrder node
variable [DecidableBinaryRel tot.le]
instantiate btwn : Between node


open Between TotalOrder

relation leader : node -> Prop
relation pending : node -> node -> Prop

#gen_state

after_init {
  leader _ := False;
  pending _ _ := False
}

action send (n next : node) = {
  require n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z);
  pending n next := True
}

action recv (sender n next : node) (havoc : Prop) = {
  require n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z);
  require pending sender n;
  if (sender = n) then
    leader n := True;
    pending sender n := havoc
  else if (le n sender) then
    pending sender n := havoc;
    pending sender n := True
  else
    pending sender n := havoc
}

safety leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#gen_spec Ring

prove_inv_init by { simp_all [initSimp, actSimp, invSimp] }

prove_inv_safe by {
  sdestruct st;
  simp [invSimp]
  rintro S _ _
  assumption
}

prove_inv_inductive by {
  intro hnext hinv
  sts_induction <;> sdestruct_all <;> solve_clause
}

sat trace [initial_state] {} by {
  simp [initSimp, actSimp]
  -- exists { leader := fun _ => false, pending := fun _ _ => false }
}

set_option trace.sauto true
set_option trace.sauto.query true
set_option trace.sauto.result true

set_option auto.smt true
set_option auto.smt.trust true

sat trace {

} by {
  bmc_sat
}

unsat trace {
  send
  assert ¬ (∃ n next, pending n next)
} by { bmc }

-- set_option pp.all true

sat trace {
  send
  assert ∃ n next, pending n next
} by {
  negate_goal
  simp only [Classical.exists_elim, Classical.not_not]
  unhygienic intros;
  sdestruct_hyps;
  simp only [initSimp, actSimp, invSimp, smtSimp, RelationalTransitionSystem.next];
  /- FIXME: this gets hit by `lean-smt` issue #100 -/
  -- admit_if_satisfiable[tot.le_refl, tot.le_trans, tot.le_antisymm, tot.le_total, btwn.btw_ring, btwn.btw_trans,
  --     btwn.btw_side, btwn.btw_total]
  sorry
}

unsat trace [trace_any] {
  any 6 actions
  assert ¬(leader L → le N L)
} by { bmc }

end Ring
