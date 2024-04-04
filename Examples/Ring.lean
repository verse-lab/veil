import LeanSts.State
import LeanSts.TransitionSystem
import LeanSts.Auto
import Mathlib.Tactic

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

variable (node : Type)
variable [DecidableEq node] [TotalOrder node] [Between node]
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

structure Structure :=
  leader (n : node) : Bool
  pending (n1 n2 : node) : Bool

def initialState? (rs : Structure node) : Prop :=
  (∀ (n : node), ¬ rs.leader n) ∧
  (∀ (n1 n2 : node), ¬ rs.pending n1 n2)

@[simp] def send : RelationalTransitionSystem.action (Structure node) :=
  λ (st st' : Structure node) =>
    ∃ (n next : node),
      -- preconditions
      (∀ (z : node), n ≠ next ∧ ((z ≠ n ∧ z ≠ next) → btw n next z)) ∧
      -- postconditions
      st' = {st with pending := st.pending[n , next ↦ true]}

@[simp] def recv : RelationalTransitionSystem.action (Structure node) :=
  λ (st st' : Structure node) =>
    ∃ (sender n next : node) (havoc : Bool),
      -- preconditions
      (∀ (z : node), n ≠ next ∧ ((z ≠ n ∧ z ≠ next) → btw n next z)) ∧
      (st.pending sender n) ∧
      -- postconditions
      -- `pending(sender, n) := *` is modelled using `havoc`
      if sender = n then
        st' = {st with leader := st.leader[n ↦ true], pending := st.pending[sender, n ↦ havoc]}
      else
        if le n sender then
          st' = {st with pending := st.pending[sender, n ↦ havoc][sender , next ↦ true]}
        else
          st' = {st with pending := st.pending[sender, n ↦ havoc]}

-- so we don't need to add `node` explicitly to all definitions below
variable {node : Type}
variable [DecidableEq node] [TotalOrder node] [Between node]

instance System : RelationalTransitionSystem (Structure node)
  where
  init := λ st => initialState? node st
  -- TLA-style
  next := λ st st' => send node st st' ∨ recv node st st'

@[simp] def safety (st : Structure node) : Prop :=
  ∀ (N L : node), st.leader L → le N L

@[simp] def inv_1 (st : Structure node) : Prop :=
  ∀ (S D N : node), st.pending S D ∧ btw S N D → le N S

@[simp] def inv_2 (st : Structure node) : Prop :=
  ∀ (N L : node), st.pending L L → le N L

def safety_init :
  ∀ (st : Structure node), System.init st → safety st := by
  intro st
  simp only [RelationalTransitionSystem.init, safety, System, initialState?]
  rintro ⟨hleader, _hpending⟩
  intro N L hcontra
  specialize hleader L
  contradiction

@[simp] def inv (st : Structure node) : Prop :=
  safety st ∧ inv_1 st ∧ inv_2 st

def inv_init :
  ∀ (st : Structure node), System.init st → inv st := by
  intro st
  simp only [RelationalTransitionSystem.init, safety, System, initialState?]
  rintro ⟨hleader, hpending⟩
  apply And.intro
  {
    apply safety_init
    simp only [RelationalTransitionSystem.init, initialState?]
    constructor
    { exact hleader }
    { exact hpending }
  }
  apply And.intro
  {
    rintro S D N ⟨hcontra, _hbtw⟩
    specialize hpending S D
    contradiction
  }
  {
    intro N L hcontra
    specialize hpending L L
    contradiction
  }

set_option maxHeartbeats 2000000

theorem inv_inductive :
  ∀ (st st' : Structure node), System.next st st' → inv st → inv st' := by
  intro st st' hnext ⟨hsafety, hinv_1, hinv_2⟩
  rcases hnext with hsend | hrecv
  { -- send
    rcases hsend with ⟨n, next, hpre, hpost⟩
    simp only [inv, safety, inv_1, inv_2, hpost]
    apply And.intro
    { apply hsafety }
    apply And.intro
    { -- inv_1
      simp_all
      duper [btw_ring, btw_side, hpre, hinv_1] {portfolioInstance := 1}
    }
    { -- inv_2
      simp_all
      duper [hpre, hinv_2] {portfolioInstance := 1}
    }
  }
  { -- recv
    rw [recv] at hrecv
    -- NOTE: hpre1 is unused, so it's not actually needed as a precondition for `recv` (?)
    rcases hrecv with ⟨sender, n, next, havoc, hpre1, hpre2, hpost⟩
    split_ifs at hpost with cond1 cond2 <;> rw [hpost]
    {
      apply And.intro
      { -- safety
        simp_all
        duper [hsafety, hinv_1, hinv_2, cond1, hpre2] {portfolioInstance := 1}
      }
      apply And.intro
      { -- inv_1
        simp_all
        intro S D N; split_ifs with cond <;> duper [hinv_1, cond, hpre2] {portfolioInstance := 1}
      }
      { -- inv_2
        simp_all
        intro N L; split_ifs with cond <;> duper [hinv_2, cond, hpre2] {portfolioInstance := 1}
      }
    }
    { -- recv, inner if
      apply And.intro
      { apply hsafety }
      apply And.intro
      { -- inv_1
        simp only [inv_1, updateFn2_unfold, Bool.and_eq_true, decide_eq_true_eq,
          Bool.ite_eq_true_distrib, and_imp]
        rintro S D N
        split_ifs with cond3 cond4
        { intro _ hbtw
          simp_all only [ne_eq, and_imp]
          by_cases hn: (N = n)
          { simp_all }
          {
            apply (hinv_1 sender n)
            apply And.intro
            { assumption }
            have Hn : _ := btw_next _  (by simp; apply hpre1)
            have ht : _ := btw_total sender N n
            rcases ht with h | h | h | h | h
            { assumption }
            { duper [h, Hn, hbtw, btw_ring, btw_trans] }
            { duper [h, hbtw, btw_irreflexive'] }
            { contradiction }
            { contradiction }
          }
        }
        {
          intro _ Hbtw
          apply (hinv_1 S D N)
          apply And.intro
          { simpa only [cond4] }
          { assumption }
        }
        { intro h1 h2; apply hinv_1; apply And.intro <;> assumption }
      }
      {
        -- inv_2
        simp only [inv_2, updateFn2_unfold, Bool.and_eq_true, decide_eq_true_eq,
          Bool.ite_eq_true_distrib]
        intro N L
        split_ifs with cond3 cond4
        { intro _
          rw [safety] at hsafety
          rw [inv_1] at hinv_1
          rw [inv_2] at hinv_2
          by_cases hl: (st.leader L)
          { apply hsafety; assumption }
          rcases cond3 with ⟨cond3a, cond3b⟩
          -- have heq : (sender = next) := by { rw [← cond3.1]; simp only [cond3.2] }
          -- simp_all
          subst_vars
          specialize (hpre1 N)
          rcases hpre1 with ⟨_, hpre1⟩
          by_cases H:(N ≠ n ∧ N ≠ L)
          { simp_all
            duper [hinv_1, hpre1, hpre2, btw_ring]
          }
          {
            simp_all
            by_cases Hn: (N = n)
            { simp_all }
            { simp_all
              apply TotalOrder.le_refl
            }
          }
        }
        {
          intro _
          rcases cond4 with ⟨cond5, cond6⟩
          rw [←cond5, ←cond6] at hpre2
          apply (hinv_2 _ _ hpre2)
        }
        { apply hinv_2 }
      }
    }
    { -- recv, just havoc
      apply And.intro
      { apply hsafety }
      apply And.intro
      { -- inv_1
        simp_all
        intro S D N; split_ifs with cond3 <;> duper [cond3, hpre2, hinv_1]
      }
      {
        -- inv_2
        simp_all
        intro N L ; split_ifs with cond3 <;> duper [cond2, cond3, TotalOrder.le_refl, hinv_2]
      }
    }
  }

end Ring
