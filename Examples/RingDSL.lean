import LeanSts.State
import LeanSts.TransitionSystem
import LeanSts.Tactics
import LeanSts.WP
-- import Mathlib.Tactic
import LeanSts.DSL

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

theorem btw_irreflexive : ∀ (n m : node),  ¬ btw m n n := by
  duper [btw_side] {portfolioInstance := 1}

theorem btw_irreflexive' : ∀ (n m : node), ¬ btw m m n := by
  duper [btw_ring, btw_side] {portfolioInstance := 1}

theorem btw_arg : ∀ (a b c : node), btw a b c →
  ¬ a = b ∧ ¬ a = c ∧ ¬ b = c := by
  duper [btw_ring, btw_trans, btw_side, Between.btw_total] {portfolioInstance := 1}

theorem btw_next :
  (∀ (z : node), n ≠ next ∧ ((z ≠ n ∧ z ≠ next) → btw n next z)) →
  (∀ (z : node), ¬ btw n z next) := by
  duper [btw_ring, btw_trans, btw_side, Between.btw_total] {portfolioInstance := 1}

theorem btw_opposite
  (Hn : ∀ (z : node), ¬ btw n z next = true)
  (h1 : btw sender N next = true)
  (h2 : btw sender n N = true) :
  False := by
  duper [Hn, h1, h2, btw_ring, btw_trans] {portfolioInstance := 1}

open Between TotalOrder

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

#print State

after_init {
  leader _ := false;
  pending _ _ := false
}

#print initalState?

action send (n next : node) = {
  require ∀ (z : node), n ≠ next ∧ ((z ≠ n ∧ z ≠ next) → Between.btw n next z);
  pending n next := true
}

-- action recv (sender n next : node) (havoc : Bool) = fun st st' =>
--   wp _ (Eq st') [lang| require pending sender ]

action recv (sender n next : node) (havoc : Bool) = {
  require ∀ (z : node), n ≠ next ∧ ((z ≠ n ∧ z ≠ next) → btw n next z);
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

safety ∀ (N L : node), leader L → le N L
invariant ∀ (S D N : node), pending S D ∧ btw S N D → le N S
invariant ∀ (N L : node), pending L L → le N L

#gen_spec

prove_safety_init by {
  sdestruct st;
  simp [actSimp]
  rintro ⟨rlf⟩
  simp
}

prove_inv_init by {
  sdestruct st;
  simp [actSimp]
  rintro ⟨rlf⟩ ⟨rlf⟩
  simp
}

set_option maxHeartbeats 2000000

set_option auto.smt true
set_option auto.smt.trust true

prove_inv_inductive by {
  intro hnext hinv
  sts_induction <;> (sdestruct) <;> repeat
  (
    sdestruct st1 st2;
    simp [sts, actSimp] at hinv htr ⊢;
    (try dsimp at htr)
    auto [TotalOrder.le_refl,
      TotalOrder.le_trans,
      TotalOrder.le_antisymm,
      TotalOrder.le_total,
      Between.btw_ring,
      Between.btw_trans,
      Between.btw_side,
      Between.btw_total,
      hinv, htr]
  )
}

end Ring
