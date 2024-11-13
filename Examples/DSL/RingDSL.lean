import LeanSts.State
import LeanSts.TransitionSystem
import LeanSts.Tactic
import LeanSts.DSL

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
instantiate tot : TotalOrder node
instantiate dec_le : DecidableBinaryRel tot.le
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
  -- message may or may not be removed
  -- this models that multiple messages might be in flight
  pending sender n := havoc;
  if (sender = n) {
    leader n := True
  }
  else {
    -- pass message to next node
    if (le n sender) {
      pending sender next := True
    }
  }
}

safety [single_leader] leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#gen_spec Ring

-- set_option trace.sauto.query true
-- set_option trace.sauto.result true

#check_invariants

prove_inv_init by { simp_all [initSimp, actSimp, wlp, invSimp] }

prove_inv_safe by {
  sdestruct st;
  simp [invSimp]
  rintro S _ _
  assumption
}

prove_inv_inductive by {
  intro hnext hinv
  sts_induction <;> sdestruct_goal <;> solve_clause
}

sat trace [initial_state] {} by {
  simp [initSimp, actSimp, wlp]
  -- exists { leader := fun _ => false, pending := fun _ _ => false }
}

sat trace {
  send
  assert (∃ n next, pending n next)
} by { bmc_sat }


sat trace [can_elect_leader_explicit] {
  send
  assert (∃ n next, pending n next)
  recv
  recv
  assert (∃ l, leader l)
} by { bmc_sat }

sat trace [can_elect_leader] {
  any 3 actions
  assert (∃ l, leader l)
} by { bmc_sat }

unsat trace {
  send
  assert (¬ ∃ n next, pending n next)
} by { bmc }

sat trace {
  send
  assert (∃ n next, pending n next)
} by { bmc_sat }

unsat trace [trace_any] {
  any 6 actions
  assert ¬ (leader L → le N L)
} by { bmc }

end Ring
