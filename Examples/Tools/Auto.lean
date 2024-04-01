import Auto
import Mathlib.Tactic

structure TotalOrder (t : Type) :=
  -- relation: total order
  le (x y : t) : Bool
  -- axioms
  -- le_refl       (x : t) : le x x
  -- le_trans  (x y z : t) : le x y → le y z → le x z
  -- le_antisymm (x y : t) : le x y → le y x → x = y
  -- le_total    (x y : t) : le x y ∨ le y x

def x : TotalOrder Nat := {
  le := (· ≤ ·)
  -- le_refl := by simp
  -- le_trans := by {
  --   intro x y z; simp only [decide_eq_true_eq]
  --   apply LE.le.trans
  -- }
  -- le_antisymm := by {
  --   intro x y; simp only [decide_eq_true_eq]
  --   apply LE.le.antisymm
  -- }
  -- le_total := by {
  --   intro x y; simp only [decide_eq_true_eq]
  --   sorry
  -- }
}

set_option auto.smt true
set_option auto.smt.trust true

set_option trace.auto.tactic true
set_option trace.auto.printLemmas true

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.smt.model true
-- set_option trace.auto.smt.proof false


def f (x : Nat) : Nat := x + 1

example : ∀ (f : Nat → Nat), (∀ x, f x = x + 1) → ∃ (x : Nat), f x + 1 = 2 := by
  auto

example :  ∃ (x : Nat), f x + 1 = 2 := by
  unfold f
  auto

example : ∃ (x : Nat), x + 3 = 7 := by
  -- simp only [Nat.succ.injEq, exists_eq]
  auto

example : ∀ (x : Nat), x = x + 1 := by
  auto

example (x : α) (y : List α) : List.head? (x :: y) = .some x := by
  -- have h₁ : List.head? (α := α) [] = .none := rfl
  have h₂ : ∀ (x : α) (ys : _), List.head? (x :: ys) = .some x := fun _ _ => rfl
  auto

example : ∃ (x : TotalOrder Nat), x.le 3 7 := by
  auto -- lamSort2STermAux :: Unexpected error. Higher order input?

#check Nat.le
def nat_le (x y : Nat) : Bool :=
  match x, y with
  | 0, _ => true
  | _, 0 => false
  | Nat.succ x, Nat.succ y => nat_le x y

example : ∃ (x y : Nat), nat_le (x + 5) 7 = true := by
  auto
  -- !! This is actually false -- it seems the encoding into SMT says
  -- nothing about the definition of nat_le!

def always_false (x : Int) : Bool := false
lemma af_false (x : Nat) : always_false x = false := rfl
example : ∃ (n : Int), always_false n = true := by
  auto [af_false]
  -- lemma `af_false` doesn't get translated to SMT

example : ∃ (n : Nat), always_false n = true := by
  auto

structure concrete_TotalOrder :=
  le (x y : Nat) : Bool

example : ∃ (x : concrete_TotalOrder), x.le 3 7 := by
  auto -- lamSort2STermAux :: Unexpected error. Higher order input?
  -- so this isn't due to the type polymorphism of TotalOrder

example : ∃ (le : Nat → Nat → Bool), le 3 7 := by
  auto -- lamSort2STermAux :: Unexpected error. Higher order input?

inductive Zone where
  | Z1 | Z2 | Z3 | Z4
  deriving Inhabited, Repr, DecidableEq

abbrev Area : Type := Int

def Zone.MinArea1 : Zone → Area
  | .Z1    => 10000
  | .Z2    => 5000
  | .Z3     => 3500
  | .Z4     => 2500

example (x: Zone) : x.MinArea1 >= 2500 := by cases x <;> simp [Zone.MinArea1] -- succeeds
example (x: Zone) : x.MinArea1 >= 2500 := by
  unfold Zone.MinArea1
  cases x <;> auto
