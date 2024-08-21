import LeanSts.TransitionSystem
import LeanSts.State
import LeanSts.Tactic
import Mathlib.Tactic

-- TODO: find a better way to model sorts than variables
section Bank
-- sort account
variable (account : Type) [DecidableEq account]

structure BankState where
  balance : account → Int

def initialState : BankState account := { balance := λ _ => 0 }

@[simp] def deposit : RelationalTransitionSystem.action (BankState account) :=
  λ (st st' : BankState account) =>
    ∃ (a : account) (amount : Int),
      amount ≥ 0 ∧ st'.balance = st.balance[a ↦ st.balance a + amount]

@[simp] def withdraw : RelationalTransitionSystem.action (BankState account) :=
  λ (st st' : BankState account) =>
    ∃ (a : account) (amount : Int),
      amount ≥ 0 ∧ st.balance a ≥ amount ∧ st'.balance = st.balance[a ↦ st.balance a - amount]

inductive BankTransition (st st' : BankState account) where
  | deposit : deposit account st st' → BankTransition st st'
  | withdraw : withdraw account st st' → BankTransition st st'

end Bank

@[simp] def safety (st : BankState Int) : Prop := (∀ acc, st.balance acc ≥ 0)

instance BankSystem : RelationalTransitionSystem (BankState Int) where
  init := λ st => st = initialState Int
  -- TLA-style
  -- next := λ st st' => deposit Int st st' ∨ withdraw Int st st'
  -- CIC-style
  next := λ st st' => ∃ (_t : BankTransition Int st st'), True
  safe := safety
  inv := safety

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
    simp only [post, ge_iff_le]
    split_ifs with eq
    { specialize safe acc; linarith }
    { apply safe }
  }
  | withdraw tr => {
    simp only [withdraw] at tr
    rcases tr with ⟨acc, amount, ⟨pre1, pre2, post⟩⟩
    intro acc'
    simp only [post, ge_iff_le]
    split_ifs with eq
    { specialize safe acc; linarith }
    { apply safe }
  }

theorem bank_safety_smt :
  ∀ st st', BankSystem.next st st' → safety st → safety st' := by
  intro st st' hnext hinv
  sts_induction <;> repeat'
  (
    sdestruct st st';
    simp [RelationalTransitionSystem.inv] at hinv hnext ⊢
    sauto [hinv, hnext]
  )
