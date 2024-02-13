import Smt
import Mathlib.Tactic

-- set_option smt.solver.kind "z3"
theorem modus_ponens (p q : Prop) : p → (p → q) → q := by
  smt

#print modus_ponens
-- set_option pp.notation false

structure TotalOrder (t : Type) :=
  -- relation: total order
  le (x y : t) : Bool
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x


def x : TotalOrder Nat := {
  le := (· ≤ ·)
  le_refl := by simp
  le_trans := by {
    intro x y z; simp only [decide_eq_true_eq]
    apply LE.le.trans
  }
  le_antisymm := by {
    intro x y; simp only [decide_eq_true_eq]
    apply LE.le.antisymm
  }
  le_total := by {
    intro x y; simp only [decide_eq_true_eq]
    sorry
  }
}

-- This crashes the Lean server:
-- def X : Type := Fin 5
-- example inst : ∃ x : TotalOrder Nat, True := by
--   smt
