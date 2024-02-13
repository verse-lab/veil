import Mathlib.Tactic
import Mathlib.Testing.SlimCheck.Testable
import Mathlib.Testing.SlimCheck.Sampleable
import Mathlib.Testing.SlimCheck.Functions
import Mathlib.Testing.SlimCheck.Gen

example (xs : List ℕ) (w : ∃ x ∈ xs, x < 3) : ∀ y ∈ xs, y < 5 := by
 slim_check

example : ∀ (x : Nat), x < 100 := by slim_check -- success (!!!)
