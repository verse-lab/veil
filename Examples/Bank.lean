import LeanSts.TransitionSystem
import LeanSts.State
import Mathlib.Tactic

-- TODO: find a better way to model sorts than variables
section Bank
-- sort account
variable (account : Type) [DecidableEq account]

structure BankState where
  balance : account → Int

def initialState : BankState account := { balance := λ _ => 0 }

def deposit : RelationalTransitionSystem.action (BankState account) :=
  λ (st st' : BankState account) =>
    ∃ (a : account) (amount : Int),
      amount ≥ 0 ∧ st'.balance = st.balance[a ↦ st.balance a + amount]

def withdraw : RelationalTransitionSystem.action (BankState account) :=
  λ (st st' : BankState account) =>
    ∃ (a : account) (amount : Int),
      amount ≥ 0 ∧ st.balance a ≥ amount ∧ st'.balance = st.balance[a ↦ st.balance a - amount]

inductive BankTransition (st st' : BankState account) where
  | deposit : deposit account st st' → BankTransition st st'
  | withdraw : withdraw account st st' → BankTransition st st'

end Bank

instance BankSystem : RelationalTransitionSystem (BankState Int) where
  init := λ st => st = initialState Int
  -- TLA-style
  -- next := λ st st' => deposit Int st st' ∨ withdraw Int st st'
  -- CIC-style
  next := λ st st' => ∃ (_t : BankTransition Int st st'), True

-- def BankSystem : RelationalTransitionSystem (BankState Int) := {
--   init := λ st => st = initialState Int
--   next := λ st st' => ∃ (_t : BankTransition Int st st'), True
-- }

def safety (st : BankState Int) : Prop := (∀ acc, st.balance acc ≥ 0)

theorem bank_safety_init :
  ∀ st, BankSystem.init st → safety st := by
  intro st
  simp only [RelationalTransitionSystem.init, safety, BankSystem, initialState]
  intro h acc
  simp only [h, le_refl]

-- TODO: automate this fully
theorem bank_safety_inductive :
  ∀ st st', BankSystem.next st st' → safety st → safety st' := by
  intro st st' tr safe
  simp only [BankSystem, RelationalTransitionSystem.next] at tr
  rcases tr with ⟨tr, _⟩
  rw [safety] at safe ⊢
  cases tr with
  | deposit tr  => {
    simp only [deposit] at tr
    rcases tr with ⟨acc, amount, pre, post⟩
    intro acc'
    simp only [post, updateFn_unfold, ge_iff_le]
    split_ifs with eq
    { specialize safe acc; linarith }
    { apply safe }
  }
  | withdraw tr => {
    simp only [withdraw] at tr
    rcases tr with ⟨acc, amount, ⟨pre1, pre2, post⟩⟩
    intro acc'
    simp only [post, updateFn_unfold, ge_iff_le]
    split_ifs with eq
    { specialize safe acc; linarith }
    { apply safe }
  }

-- set_option trace.Meta.synthInstance true
-- example : ∀ n m : Nat, n + m = m + n := by
--   slim_check
