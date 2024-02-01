import LeanSts.Basic
import LeanSts.Classes
import LSpec

-- TODO: find a better way to model sorts than variables
section Bank
-- sort account
variable (account : Type) [DecidableEq account]

structure BankState where
  balance : account → Int

def updateFn [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  λ x => if x = a then b else f x
notation st"[ " a " ↦ " b " ]" => updateFn st a b

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

#check BankSystem.init

open LSpec

#lspec
  test "four equals four" (4 = 4) $
  -- This requires a Testable instance, which requires DecidableEq (?) for BankState
  -- test "init equals init" (BankSystem.init (initialState Int)) $
  test "true" True

#lspec check "add_comm" $ ∀ n m : Nat, n + m = m + n
