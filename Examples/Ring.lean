import LeanSts.State
import LeanSts.TransitionSystem
import LeanSts.Tactic
import Mathlib.Tactic

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

variable (node : Type)
variable [DecidableEq node] [tot : TotalOrder node] [DecidableRel tot.le] [Between node]

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
  (Hn : ∀ (z : node), ¬ btw n z next)
  (h1 : btw sender N next)
  (h2 : btw sender n N) :
  False := by
  duper [Hn, h1, h2, btw_ring, btw_trans] {portfolioInstance := 1}

structure Structure :=
  leader (n : node) : Prop
  pending (n1 n2 : node) : Prop

@[simp] def initialState? (rs : Structure node) : Prop :=
  (∀ (n : node), ¬ rs.leader n) ∧
  (∀ (n1 n2 : node), ¬ rs.pending n1 n2)

@[simp] def send : RelationalTransitionSystem.action (Structure node) :=
  λ (st st' : Structure node) =>
    ∃ (n next : node),
      -- preconditions
      (∀ (z : node), n ≠ next ∧ ((z ≠ n ∧ z ≠ next) → btw n next z)) ∧
      -- postconditions
      st' = {st with pending := st.pending[n , next ↦ True]}

@[simp] def recv : RelationalTransitionSystem.action (Structure node) :=
  λ (st st' : Structure node) =>
    ∃ (sender n next : node) (havoc : Prop),
      -- preconditions
      (∀ (z : node), n ≠ next ∧ ((z ≠ n ∧ z ≠ next) → btw n next z)) ∧
      (st.pending sender n) ∧
      -- postconditions
      -- `pending(sender, n) := *` is modelled using `havoc`
      if sender = n then
        st' = {st with leader := st.leader[n ↦ True], pending := st.pending[sender, n ↦ havoc]}
      else
        if le n sender then
          st' = {st with pending := st.pending[sender, n ↦ havoc][sender , next ↦ True]}
        else
          st' = {st with pending := st.pending[sender, n ↦ havoc]}

-- so we don't need to add `node` explicitly to all definitions below
variable {node : Type}
variable [DecidableEq node] [tot : TotalOrder node] [DecidableRel tot.le] [btwn : Between node]

@[simp] def safety (st : Structure node) : Prop :=
  ∀ (N L : node), st.leader L → le N L

@[simp] def inv_1 (st : Structure node) : Prop :=
  ∀ (S D N : node), st.pending S D ∧ btw S N D → le N S

@[simp] def inv_2 (st : Structure node) : Prop :=
  ∀ (N L : node), st.pending L L → le N L
@[simp] def inv' (st : Structure node) : Prop :=
  safety st ∧ inv_1 st ∧ inv_2 st

instance System : RelationalTransitionSystem (Structure node)
  where
  init := λ st => initialState? node st
  -- TLA-style
  next := λ st st' => send node st st' ∨ recv node st st'
  safe := safety
  inv := inv'

open RelationalTransitionSystem
def safety_init :
  ∀ (st : Structure node), System.init st → safety st := by
  intro st
  simp only [RelationalTransitionSystem.init, safety, System, initialState?]
  rintro ⟨hleader, _hpending⟩
  intro N L hcontra
  specialize hleader L
  contradiction


open RelationalTransitionSystem

def inv_init' :
  ∀ (st : Structure node), init st → inv st := by
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

set_option auto.smt true
set_option auto.smt.trust true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
-- set_option trace.auto.smt.stderr true

set_option trace.smt true
set_option trace.smt.solve true
set_option trace.smt.translate.query true
-- without this we get "result: unknown (INCOMPLETE)"
set_option smt.solver.finitemodelfind true

theorem inv_inductive_smt :
  ∀ (st st' : Structure node), System.next st st' → inv st → inv st' := by
  intro st st' hnext hinv
  sts_induction <;> (dsimp only [RelationalTransitionSystem.inv, inv']; sdestruct) <;> repeat
  (
    sdestruct st st' tot btwn;
    simp [RelationalTransitionSystem.inv] at hinv hnext ⊢;
    trust_smt [tot.le_refl, tot.le_trans, tot.le_antisymm, tot.le_total,
      btwn.btw_ring, btwn.btw_trans, btwn.btw_side, btwn.btw_total,
      hinv, hnext
    ]
    -- auto [tot.le_refl, tot.le_trans, tot.le_antisymm, tot.le_total,
    --   btwn.btw_ring, btwn.btw_trans, btwn.btw_side, btwn.btw_total,
    --   hinv, hnext
    -- ]
  )

end Ring
