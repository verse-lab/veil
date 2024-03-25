import LeanSts.State
import LeanSts.TransitionSystem
import LeanSts.Testing
import LeanSts.SMT
import Duper

set_option auto.smt true
set_option auto.smt.trust true
-- set_option trace.auto.printLemmas true
-- set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true

-- https://github.com/aman-goel/ivybench/blob/5db7eccb5c3bc2dd14dfb58eddb859b036d699f5/ex/ivy/ring.ivy

section Ring

structure TotalOrder (t : Type) :=
  -- relation: total order
  le (x y : t) : Bool
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x

structure Between (node : Type) :=
  -- relation: btw represents a ring
  -- read: y is between x and z
  btw (x y z : node) : Bool
  -- axioms
  btw_ring    (x y z : node) : btw x y z → btw y z x
  btw_trans (w x y z : node) : btw w x y → btw w y z → btw w x z
  btw_side    (w x y : node) : btw w x y → ¬ btw w y x
  btw_total   (w x y : node) : btw w x y ∨ btw w y x ∨ w = x ∨ w = y ∨ x = y

theorem btw_irreflexive : ∀ (n m : α), (h : Between α) → ¬ h.btw m n n := by
  rintro n m ⟨btw, btw_ring, btw_trans, btw_side, btw_total⟩
  dsimp
  -- NOTE: this works after destruction of Between, but not before
  --  because the monomorphization procedure is not good enough
  -- auto
  -- proof in Lean
  duper [btw_side] {portfolioInstance := 1}
  -- constructive proof:
  -- intro h
  -- specialize (btw_side _ _ _ h)
  -- contradiction

theorem btw_irreflexive' : ∀ (n m : α), (h : Between α) → ¬ h.btw m m n := by
  rintro n m ⟨btw, btw_ring, btw_trans, btw_side, btw_total⟩
  dsimp
  duper [btw_ring, btw_side] {portfolioInstance := 1}

theorem btw_arg : ∀ (a b c : α), (h : Between α) → h.btw a b c →
  ¬ a = b ∧ ¬ a = c ∧ ¬ b = c := by
  rintro a b c ⟨btw, btw_ring, btw_trans, btw_side, btw_total⟩ h
  simp_all
  duper [btw_ring, btw_trans, btw_side, btw_total, h]

-- set_option maxHeartbeats 2000000

-- FIXME:
-- should it be `b.btw next n z`?

theorem btw_next (b : Between node):
  (∀ (z : node), n ≠ next ∧ ((z ≠ n ∧ z ≠ next) → b.btw n next z)) →
  (∀ (z : node), ¬ b.btw n z next) := by
  intro h z hbtw
  rcases b with ⟨btw, btw_ring, btw_trans, btw_side, btw_total⟩
  duper [h, hbtw, btw_ring, btw_trans, btw_side, btw_total]


structure Structure (node : Type) [DecidableEq node]  :=
  -- immutable relations & axioms
  total_order : TotalOrder node
  between : Between node
  -- actual state
  leader (n : node) : Bool
  pending (n1 n2 : node) : Bool

def initialState? (node : Type) [DecidableEq node] (rs : Structure node) : Prop :=
  (∀ (n : node), ¬ rs.leader n) ∧
  (∀ (n1 n2 : node), ¬ rs.pending n1 n2)

def send (node : Type) [DecidableEq node] : RelationalTransitionSystem.action (Structure node) :=
  λ (st st' : Structure node) =>
    ∃ (n next : node),
      -- preconditions
      (∀ (z : node), n ≠ next ∧ ((z ≠ n ∧ z ≠ next) → st.between.btw n next z)) ∧
      -- postconditions
      st' = {st with pending := st.pending[n , next ↦ true]}

def recv (node : Type) [DecidableEq node] : RelationalTransitionSystem.action (Structure node) :=
  λ (st st' : Structure node) =>
    ∃ (sender n next : node) (havoc : Bool),
      -- preconditions
      (∀ (z : node), n ≠ next ∧ ((z ≠ n ∧ z ≠ next) → st.between.btw n next z)) ∧
      (st.pending sender n) ∧
      -- postconditions
      -- `pending(sender, n) := *` is modelled using `havoc`
      if sender = n then
        st' = {st with leader := st.leader[n ↦ true], pending := st.pending[sender, n ↦ havoc]}
      else
        if st.total_order.le n sender then
          st' = {st with pending := st.pending[sender, n ↦ havoc][sender , next ↦ true]}
        else
          st' = {st with pending := st.pending[sender, n ↦ havoc]}

instance System {node : Type} [DecidableEq node] :
  RelationalTransitionSystem (Structure node)
  where
  init := λ st => initialState? node st
  -- TLA-style
  next := λ st st' => send node st st' ∨ recv node st st'

def safety {node : Type} [DecidableEq node] (st : Structure node) : Prop :=
  ∀ (N L : node), st.leader L → st.total_order.le N L

def inv_1 {node : Type} [DecidableEq node] (st : Structure node) : Prop :=
  ∀ (S D N : node), st.pending S D ∧ st.between.btw S N D → st.total_order.le N S

def inv_2 {node : Type} [DecidableEq node] (st : Structure node) : Prop :=
  ∀ (N L : node), st.pending L L → st.total_order.le N L

-- set_option pp.notation false

def safety_init {node : Type} [DecidableEq node] :
  ∀ (st : Structure node), System.init st → safety st := by
  intro st
  simp only [RelationalTransitionSystem.init, safety, System, initialState?]
  rintro ⟨hleader, _hpending⟩
  intro N L hcontra
  specialize hleader L
  contradiction

def inv {node : Type} [DecidableEq node] (st : Structure node) : Prop :=
  safety st ∧ inv_1 st ∧ inv_2 st

def inv_init {node : Type} [DecidableEq node] :
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

theorem inv_inductive {node : Type} [DecidableEq node] :
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
      rw [inv_1] at hinv_1
      rintro S D N ⟨hp', hbtw'⟩
      apply (hinv_1 S D N)
      apply And.intro
      {
        simp at hp'; apply hp'
        intro Hs Hd
        -- suspect there is a contradiction with hpre and some of the `btw` axioms
        simp only [Hs, Hd] at hbtw'
        rcases (hpre N) with ⟨hpre1, hpre2⟩
        apply (st.between.btw_side _ _ _ hbtw')
        apply hpre2
        apply And.intro
        {
          intro Hn
          rw [Hn] at hbtw'
          have Hx : _ := st.between.btw_ring _ _ _ hbtw'
          have Hy : _ := st.between.btw_side _ _ _ hbtw'
          contradiction
        }
        {
          intro Hn
          rw [Hn] at hbtw'
          have Hx : _ := st.between.btw_side _ _ _ hbtw'
          contradiction
        }

      }
      { exact hbtw' }
    }
    { -- inv_2
      rw [inv_2] at hinv_2
      simp only [updateFn2_unfold, Bool.and_eq_true, decide_eq_true_eq, ite_eq_left_iff, not_and]
      rintro N L hp'
      apply hinv_2
      apply hp'
      intro Hn
      rw [Hn]
      rcases (hpre L) with ⟨Hnn, _⟩
      assumption
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
        simp only [safety, updateFn_unfold, ite_eq_left_iff]
        rw [cond1] at hpre2
        rintro N L hp'
        cases Hx : (L == n)
        {
          simp only [beq_eq_false_iff_ne, ne_eq] at Hx
          specialize (hp' Hx)
          apply hsafety
          assumption
        }
        {
          simp only [beq_iff_eq] at Hx
          rw [←Hx] at hpre2
          apply hinv_2
          assumption
        }
      }
      apply And.intro
      { -- inv_1
        simp only [inv_1._eq_1, and_imp, updateFn2_unfold, Bool.and_eq_true, decide_eq_true_eq,
          Bool.ite_eq_true_distrib] at hinv_1 ⊢
        intro S D N
        split_ifs with cond
        {
          rcases cond with ⟨cond2, cond3⟩
          rw [←cond2, ←cond3] at hpre2
          intro _
          apply (hinv_1 _ _ _ hpre2)
        }
        { apply hinv_1 }

      }
      { -- inv_2
        simp [inv_2] at hinv_2 ⊢
        intro N L
        split_ifs with cond
        {
          rcases cond with ⟨cond2, cond3⟩
          rw [←cond2, ←cond3] at hpre2
          intro _
          apply (hinv_2 _ _ hpre2)
        }
        { apply hinv_2 }
      }
    }
    { -- recv, inner if
      apply And.intro
      { apply hsafety}
      apply And.intro
      { -- inv_1
        simp only [inv_1._eq_1, updateFn2_unfold, Bool.and_eq_true, decide_eq_true_eq,
          Bool.ite_eq_true_distrib, and_imp]
        rintro S D N
        split_ifs with cond3 cond4
        { intro _ hbtw
          simp_all only [ne_eq, and_imp]
          -- `N` is a node before `sender` (and therefore before `n`)
          -- thus the fact that a message reached `n` must mean that `N <= sender`
          -- rw [inv_1] at hinv_1
          -- rw [inv_2] at hinv_2
          -- rcases st with ⟨⟨le, le_refl, le_trans, le_antisymm, le_total⟩, ⟨btw, btw_ring, btw_trans, btw_side, btw_total⟩, leader, pending⟩
          -- simp_all
          -- Times out:
          -- duper [hinv_1, hinv_2, hpre1, hpre2, cond1, cond2, cond3, hbtw, le_refl, le_trans, le_antisymm, le_total, btw_ring, btw_trans, btw_side, btw_total]
          by_cases hn: (N = n)
          { simp_all }
          {
            apply (hinv_1 sender n)
            apply And.intro
            { assumption }
            have Hn : _ := btw_next _  (by simp; apply hpre1)
            have ht : _ := st.between.btw_total sender N n
            rcases ht with h | h | h | h | h
            { assumption }
            {
              rcases st with ⟨tot, ⟨btw, btw_ring, btw_trans, btw_side, btw_total⟩, leader, pending⟩
              simp_all
              -- FIXME: how to prove this manually?
              duper [h, Hn, hbtw, btw_ring, btw_trans, btw_side, btw_total]
            }
            {
              simp [h] at hbtw
              have hcontra : _ := btw_irreflexive' _ _ st.between hbtw
              contradiction
            }
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
        simp only [inv_2._eq_1, updateFn2_unfold, Bool.and_eq_true, decide_eq_true_eq,
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
            apply hinv_1
            { apply hpre2 }
            apply st.between.btw_ring
            assumption
          }
          {
            simp_all
            by_cases Hn: (N = n)
            { simp_all }
            { simp_all
              apply st.total_order.le_refl
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
        simp only [inv_1._eq_1, updateFn2_unfold, Bool.and_eq_true, decide_eq_true_eq,
          Bool.ite_eq_true_distrib, and_imp]
        intro S D N
        split_ifs with cond3
        {
          intro _ Hbtw
          rcases cond3 with ⟨cond4, cond5⟩
          rw [←cond4, ←cond5] at hpre2
          apply (hinv_1 _ _ _ (And.intro hpre2 Hbtw))
        }
        { intro h1 h2; apply hinv_1; apply And.intro <;> assumption }
      }
      {
        -- inv_2
        simp only [inv_2._eq_1, updateFn2_unfold, Bool.and_eq_true, decide_eq_true_eq,
          Bool.ite_eq_true_distrib]
        intro N L
        split_ifs with cond3
        {
          intro _
          rcases cond3 with ⟨cond4, cond5⟩
          rw [←cond4, ←cond5] at cond2
          have Ht : _ := st.total_order.le_refl L
          contradiction
        }
        { apply hinv_2 }
      }
    }
  }




end Ring
