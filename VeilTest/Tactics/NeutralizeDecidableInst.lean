import Veil.Util.ReplacingInstances

/-! ## Tests for `neutralizeDecidableInst` simproc

The simproc replaces any `Decidable p` instance argument with
`Classical.propDecidable p`, normalizing all decidable instances to the
classical one. -/

open Veil.Util

/-- Basic: a `Decidable` instance in a function argument gets neutralized. -/
example (p : Prop) [inst : Decidable p] :
    @decide p inst = @decide p (Classical.propDecidable p) := by
  simp only [neutralizeDecidableInstGeneral]

/-- With `ite`: the `Decidable` instance in `if` gets neutralized. -/
example (p : Prop) [inst : Decidable p] (a b : Nat) :
    @ite Nat p inst a b = @ite Nat p (Classical.propDecidable p) a b := by
  simp only [neutralizeDecidableInstGeneral]

/-- Concrete decidable instance (e.g., `Nat.decEq`). -/
example (n m : Nat) :
    @decide (n = m) (instDecidableEqNat n m) =
    @decide (n = m) (Classical.propDecidable (n = m)) := by
  simp only [neutralizeDecidableInstGeneral]

/-- Already classical: no change, `rfl` suffices. -/
example (p : Prop) :
    @decide p (Classical.propDecidable p) =
    @decide p (Classical.propDecidable p) := by
  rfl

/-- Neutralization inside a larger expression. -/
example (p : Prop) [inst : Decidable p] (f : Bool → Nat) :
    f (@decide p inst) = f (@decide p (Classical.propDecidable p)) := by
  simp only [neutralizeDecidableInstGeneral]

/-- Multiple `Decidable` instances in separate subexpressions. -/
example (p q : Prop) [instP : Decidable p] [instQ : Decidable q] :
    (@decide p instP, @decide q instQ) =
    (@decide p (Classical.propDecidable p), @decide q (Classical.propDecidable q)) := by
  simp only [neutralizeDecidableInstGeneral]

/-- Decidable instance with arguments: `DecidableEq` is `a → a → Decidable (· = ·)`. -/
example (n m : Nat) (inst : DecidableEq Nat) :
    @decide (n = m) (inst n m) =
    @decide (n = m) (Classical.propDecidable (n = m)) := by
  simp only [neutralizeDecidableInstGeneral]

/-- Decidable instance with one argument: `∀ x, Decidable (p x)`. -/
example (p : Nat → Prop) (inst : ∀ x, Decidable (p x)) (n : Nat) :
    @decide (p n) (inst n) =
    @decide (p n) (Classical.propDecidable (p n)) := by
  simp only [neutralizeDecidableInstGeneral]

/-- Decidable instance with two arguments: `∀ x y, Decidable (r x y)`. -/
example (r : Nat → Nat → Prop) (inst : ∀ x y, Decidable (r x y)) (a b : Nat) :
    @ite Nat (r a b) (inst a b) 1 0 =
    @ite Nat (r a b) (Classical.propDecidable (r a b)) 1 0 := by
  simp only [neutralizeDecidableInstGeneral]

/-- Decidable instance deeply nested in arguments. -/
example (p : Prop) [inst : Decidable p] (f : Bool → Bool → Nat) :
    f (@decide p inst) (@decide p inst) =
    f (@decide p (Classical.propDecidable p)) (@decide p (Classical.propDecidable p)) := by
  simp only [neutralizeDecidableInstGeneral]
