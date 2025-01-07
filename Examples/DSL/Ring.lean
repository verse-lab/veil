import Veil.State
import Veil.TransitionSystem
import Veil.Tactic
import Veil.DSL
import Examples.DSL.Std

-- https://github.com/aman-goel/ivybench/blob/5db7eccb5c3bc2dd14dfb58eddb859b036d699f5/ex/ivy/ring.ivy

section Ring
open Classical

type node
instantiate tot : TotalOrder node
-- instantiate dec_le : DecidableBinaryRel tot.le
instantiate btwn : Between node


open Between TotalOrder

relation leader : node -> Prop
relation pending : node -> node -> Prop

#gen_state Ring

after_init {
  leader N := False;
  pending N M := False
}

action send (n next : node) = {
  require n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z);
  pending n next := True
}

-- requries/ensures example:
-- action send_axiomatic (n next : node) = {
--   require n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z);
--   ensure
--     pending n next = True ∧
--     ∀ n' next', n' ≠ n -> next' ≠ next ->
--       pending n next = pending_old n next
-- }

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
-- set_option sauto.smt.translator "lean-smt"
-- set_option trace.sauto.result true
-- set_option trace.sauto.debug true

#check_invariants

prove_inv_init by { simp_all [initSimp, actSimp, wlp, invSimp] }

prove_inv_safe by {
  sdestruct st;
  simp [invSimp]
}

prove_inv_inductive by {
  constructor
  . apply inv_init
  intro st st' hnext hinv
  sts_induction <;> sdestruct_goal <;> solve_clause
}

sat trace [initial_state] {} by { bmc_sat }

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
