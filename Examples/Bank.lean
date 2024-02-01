import LeanSts.Basic
import LeanSts.Classes

section Bank
-- sort account
variable (account : Type) [BEq account] [LawfulBEq account]

structure BankState where
  balance : account → Nat

def updateFn [BEq α] [LawfulBEq α] (f : α → β) (a : α) (b : β) : α → β :=
  λ x => if x == a then b else f x
notation st"[ " a " ↦ " b " ]" => updateFn st a b

def initialState : BankState account := { balance := λ _ => 0 }

def deposit : RelationalTransitionSystem.action (BankState account) :=
  λ (st st' : BankState account) =>
    ∃ (a : account) (amount : Nat),
      amount ≥ 0 ∧ st'.balance = st.balance[a ↦ st.balance a + amount]

def withdraw : RelationalTransitionSystem.action (BankState account) :=
  λ (st st' : BankState account) =>
    ∃ (a : account) (amount : Nat),
      amount ≥ 0 ∧ st.balance a ≥ amount ∧ st'.balance = st.balance[a ↦ st.balance a - amount]

end Bank


instance : RelationalTransitionSystem (BankState Nat) where
