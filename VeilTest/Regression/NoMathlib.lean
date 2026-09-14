import Veil
import Veil.Util.Permutations

/-! Behavioral contracts for Veil's standalone finite-type infrastructure. -/
open Veil

namespace NoMathlib

inductive Color where
  | red | green | blue
  deriving Repr, DecidableEq, Enumeration, FinEncodable

#guard Enumeration.allValues (α := Color) == [.red, .green, .blue]
#guard (FinEncodable.equiv Color.red).val == 0
#guard (FinEncodable.equiv Color.blue).val == 2
#guard Enumeration.allValues (α := Bool) == [true, false]
#guard TotalOrder.le true false
#guard ¬ TotalOrder.le false true

/-- Deliberate repeats must survive candidate enumeration, but not finite encoding. -/
inductive Repeated where
  | first | second
  deriving Repr, DecidableEq
instance : Enumeration Repeated where
  allValues := [.first, .second, .first]
  complete a := by cases a <;> simp

#guard Enumeration.allValues (α := Repeated) == [.first, .second, .first]
#guard FinEncodable.card Repeated == 2
example (a : Repeated) : FinEncodable.equiv.symm (FinEncodable.equiv a) = a := by simp

#guard Enumeration.allValues (α := Empty) |>.isEmpty
#guard (Enumeration.allValues (α := Fin 0 → Bool)).length == 1
#guard (Enumeration.allValues (α := Fin 2 → Bool)).length == 4
#guard FinEncodable.card (Fin 2 → Bool) == 4
#guard (fun _ : Fin 2 => false) ≠ (fun i : Fin 2 => i == 1)

/-- Proxy derivation handles sums, dependent constructor fields, and empty types. -/
inductive Choice where
  | unit
  | dep (n : Fin 3) (i : Fin (n.val + 1))
  deriving Enumeration
#guard (Enumeration.allValues (α := Choice)).length == 7

#guard Enumeration.allValues (α := Quorum 0) |>.isEmpty
#guard (Enumeration.allValues (α := Quorum 3)).length == 4
#guard (Enumeration.allValues (α := ByzNSet 3)).length == 8
example (a b : Quorum 3) : ∃ i, i ∈ a ∧ i ∈ b := Quorum.quorum_intersection a b

#guard Veil.List.permutations ([] : List Nat) == [[]]
#guard Veil.List.permutations [1, 2, 3] ==
  [[1, 2, 3], [2, 1, 3], [3, 2, 1], [2, 3, 1], [3, 1, 2], [1, 3, 2]]
#guard Veil.List.permutations [true, true] == [[true, true], [true, true]]

end NoMathlib
