import LeanSts.State
import LeanSts.TransitionSystem
import LeanSts.Tactic
import LeanSts.DSL
-- import Mathlib.Tactic


-- https://github.com/aman-goel/ivybench/blob/5db7eccb5c3bc2dd14dfb58eddb859b036d699f5/ex/ivy/ring.ivy

section Ring

class TotalOrder (t : Type) :=
  -- relation: total order
  le (x y : t) : Bool
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x

class Between (node : Type) :=
  -- relation: btw represents a ring
  -- read: y is between x and z
  btw (x y z : node) : Bool
  -- axioms
  btw_ring    (x y z : node) : btw x y z → btw y z x
  btw_trans (w x y z : node) : btw w x y → btw w y z → btw w x z
  btw_side    (w x y : node) : btw w x y → ¬ btw w y x
  btw_total   (w x y : node) : btw w x y ∨ btw w y x ∨ w = x ∨ w = y ∨ x = y

type node
instantiate DecidableEq node
instantiate TotalOrder node
instantiate Between node

open Between TotalOrder

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

after_init {
  leader _ := false;
  pending _ _ := false
}

action send (n next : node) = {
  require n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z);
  pending n next := true
}

action recv (sender n next : node) (havoc : Bool) = {
  require n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z);
  require pending sender n;
  if (sender = n) then
    leader n := true;
    pending sender n := havoc
  else if (le n sender) then
    pending sender n := havoc;
    pending sender n := true
  else
    pending sender n := havoc
}

safety leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#gen_spec

prove_inv_init by { simp_all [initSimp, actSimp, invSimp] }

prove_inv_safe by {
  sdestruct st;
  simp [invSimp]
  rintro S _ _
  assumption
}

set_option auto.smt true
set_option auto.smt.trust true

prove_inv_inductive by {
  intro hnext hinv
  sts_induction <;> sdestruct <;> solve_clause
}

sat trace [initial_state] {} by {
  exists { leader := fun _ => false, pending := fun _ _ => false }
}

unsat trace [trace_any] {
  any action
  assert ¬(leader L → le N L)
} by {
  -- TODO: write tactic for this
  sintro st0 st1
  simp only [initSimp, actSimp, invSimp, RelationalTransitionSystem.next, State.mk.injEq]
  simp_all
  duper
}

end Ring
