module

public import Veil.Util.ReplacingInstances

/-! ## Tests for the `neutralizeDecidableInst` simprocs

`neutralizeDecidableInst` replaces every `Decidable p` instance argument with
`Classical.propDecidable p`, and every instance passed unapplied, of type
`∀ xs, Decidable (p xs)`, with `fun xs => Classical.propDecidable (p xs)`.
`neutralizeDecidableInstWithExpectedType` does the same, but reads `p` off the
binder type of the surrounding application instead of the type of the
argument. -/

open Veil.Util

/-- Basic: a `Decidable` instance in a function argument gets neutralized. -/
example (p : Prop) [inst : Decidable p] :
    @decide p inst = @decide p (Classical.propDecidable p) := by
  simp only [neutralizeDecidableInst]

/-- With `ite`: the `Decidable` instance in `if` gets neutralized. -/
example (p : Prop) [inst : Decidable p] (a b : Nat) :
    @ite Nat p inst a b = @ite Nat p (Classical.propDecidable p) a b := by
  simp only [neutralizeDecidableInst]

/-- Concrete decidable instance (e.g., `Nat.decEq`). -/
example (n m : Nat) :
    @decide (n = m) (instDecidableEqNat n m) =
    @decide (n = m) (Classical.propDecidable (n = m)) := by
  simp only [neutralizeDecidableInst]

/-- Already classical: no change, `rfl` suffices. -/
example (p : Prop) :
    @decide p (Classical.propDecidable p) =
    @decide p (Classical.propDecidable p) := by
  rfl

/-- Neutralization inside a larger expression. -/
example (p : Prop) [inst : Decidable p] (f : Bool → Nat) :
    f (@decide p inst) = f (@decide p (Classical.propDecidable p)) := by
  simp only [neutralizeDecidableInst]

/-- Multiple `Decidable` instances in separate subexpressions. -/
example (p q : Prop) [instP : Decidable p] [instQ : Decidable q] :
    (@decide p instP, @decide q instQ) =
    (@decide p (Classical.propDecidable p), @decide q (Classical.propDecidable q)) := by
  simp only [neutralizeDecidableInst]

/-- Decidable instance with arguments: `DecidableEq` is `a → a → Decidable (· = ·)`. -/
example (n m : Nat) (inst : DecidableEq Nat) :
    @decide (n = m) (inst n m) =
    @decide (n = m) (Classical.propDecidable (n = m)) := by
  simp only [neutralizeDecidableInst]

/-- Decidable instance with one argument: `∀ x, Decidable (p x)`. -/
example (p : Nat → Prop) (inst : ∀ x, Decidable (p x)) (n : Nat) :
    @decide (p n) (inst n) =
    @decide (p n) (Classical.propDecidable (p n)) := by
  simp only [neutralizeDecidableInst]

/-- Decidable instance with two arguments: `∀ x y, Decidable (r x y)`. -/
example (r : Nat → Nat → Prop) (inst : ∀ x y, Decidable (r x y)) (a b : Nat) :
    @ite Nat (r a b) (inst a b) 1 0 =
    @ite Nat (r a b) (Classical.propDecidable (r a b)) 1 0 := by
  simp only [neutralizeDecidableInst]

/-- Decidable instance deeply nested in arguments. -/
example (p : Prop) [inst : Decidable p] (f : Bool → Bool → Nat) :
    f (@decide p inst) (@decide p inst) =
    f (@decide p (Classical.propDecidable p)) (@decide p (Classical.propDecidable p)) := by
  simp only [neutralizeDecidableInst]

/-- An instance passed unapplied is replaced by a lambda. -/
example (p : Nat → Prop) (inst : ∀ n, Decidable (p n)) (f : (∀ n, Decidable (p n)) → Nat) :
    f inst = f (fun n => Classical.propDecidable (p n)) := by
  simp only [neutralizeDecidableInst]

/-- `DecidableEq α` is not unfolded, so an unapplied instance of it, such as a
module parameter, is left alone. -/
example (inst : DecidableEq Nat) (f : DecidableEq Nat → Nat) (h : f inst = 0) : f inst = 0 := by
  fail_if_success simp only [neutralizeDecidableInst]
  exact h

/-! ### Actual vs. expected type

`small` plays a ghost relation: an instance for `if small n then …` found
through its body has type `Decidable (n < 5)`, while `ite` expects
`Decidable (small n)`. -/

@[reducible] def small (n : Nat) : Prop := n < 5

/-- `neutralizeDecidableInst` reads the proposition off the type of the instance. -/
example (n : Nat) (inst : Decidable (n < 5)) (h : ¬ small n) :
    @ite Nat (small n) inst 1 0 = 0 := by
  simp only [neutralizeDecidableInst]
  guard_target =ₛ @ite Nat (small n) (Classical.propDecidable (n < 5)) 1 0 = 0
  exact if_neg h

/-- `neutralizeDecidableInstWithExpectedType` reads it off the binder type of `ite`. -/
example (n : Nat) (inst : Decidable (n < 5)) (h : ¬ small n) :
    @ite Nat (small n) inst 1 0 = 0 := by
  simp only [neutralizeDecidableInstWithExpectedType]
  guard_target =ₛ @ite Nat (small n) (Classical.propDecidable (small n)) 1 0 = 0
  exact if_neg h

/-! ### Building the proofs does not unfold definitions

Generated artifacts may neutralize instances while some definitions must stay
folded. The proofs therefore keep the endpoints of every equality instead of
re-inferring them by unification, which would unfold the definition an
instance was found through. `opaqueSmall` plays such a definition: the
instances below are well-typed only after unfolding it, and it is irreducible
in the tests. -/

def opaqueSmall (n : Nat) : Prop := n < 5

/-- Has the instance binder of `VeilM.pickSuchThat`. -/
def pickLike (p : Nat → Prop) [∀ x, Decidable (p x)] : Nat := 0

def viaBody (n : Nat) : Nat := @ite Nat (opaqueSmall n) (Nat.decLt n 5) 1 0

noncomputable def viaBodyNeutralized (n : Nat) : Nat :=
  @ite Nat (opaqueSmall n) (Classical.propDecidable (n < 5)) 1 0

def viaBodyUnapplied : Nat := @pickLike (fun x => opaqueSmall x) (fun x => Nat.decLt x 5)

attribute [local irreducible] opaqueSmall in
/-- Congruence over a fully applied instance. -/
example (n : Nat) : viaBody n = viaBodyNeutralized n := by
  unfold viaBody viaBodyNeutralized
  simp only [neutralizeDecidableInst]

attribute [local irreducible] opaqueSmall in
/-- An instance passed unapplied whose type matches the binder only after
unfolding `opaqueSmall`. Guards the proof of the replacement itself: building
it by unification (e.g. `mkAppM ``funext`, or passing the endpoints to
`mkAppOptM ``Subsingleton.elim`) would have to unfold `opaqueSmall`. The
expected-type variant is needed here, since the other one takes the type from
the instance itself and never has to unify it with the binder. -/
example : viaBodyUnapplied =
    @pickLike (fun x => opaqueSmall x) (fun x => Classical.propDecidable (opaqueSmall x)) := by
  unfold viaBodyUnapplied
  simp only [neutralizeDecidableInstWithExpectedType]
