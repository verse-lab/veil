import Mathlib.Data.UInt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Veil.Frontend.DSL.State.Concrete

namespace Veil

class HashAsAddCommGroup (α : Type u) (ι : Type w) where
  op : α → ι

instance [Hashable α] : HashAsAddCommGroup α UInt64 where
  op := hash

-- TODO maybe adapt this to map structures as well, later
-- "lifting" a data structure to allow hashing while updating
-- (i.e., incremental hashing)

-- CAVEAT: `β × UInt64` is not enough; it does not carry any invariant
-- that is required for proving the `LawfulHashable` of the whole thing;
-- to maintain this invariant, need `LawfulFinsetLike`
-- CAVEAT: the update of `hashval` depends on the membership, so need to
-- do something about this
structure HashCompanioned (β : Type v) (ι : Type w)
  [DecidableEq α] [Membership α β]
  [FinsetLike β] [LawfulFinsetLike β]
  [AddCommGroup ι] [insth : HashAsAddCommGroup α ι] where
  inner : β
  hashval : ι
  invariant : hashval = (∑ a ∈ LawfulFinsetLike.toFinset inner, insth.op a)

section HashCompanioned

variable {α : Type u} {β : Type v} {ι : Type w}
  [DecidableEq α] [Membership α β]
  [FinsetLike β] [instl : LawfulFinsetLike β]
  [AddCommGroup ι] [insth : HashAsAddCommGroup α ι]

instance : Membership α (HashCompanioned β ι) where
  mem b a := a ∈ b.inner

def HashCompanioned.insert (a : α) (b : HashCompanioned β ι) (h : a ∉ b) : HashCompanioned β ι :=
  { inner := FinsetLike.insert a b.inner h
    hashval := HashAsAddCommGroup.op a + b.hashval
    invariant := by
      rw [b.invariant, instl.insert_toFinset]
      have h' : a ∉ instl.toFinset b.inner := by rw [← instl.toFinset_mem_iff] ; exact h
      rw [Finset.sum_insert' (M := ι) h']
  }

def HashCompanioned.erase (a : α) (b : HashCompanioned β ι) (h : a ∈ b) : HashCompanioned β ι :=
  { inner := FinsetLike.erase a b.inner h
    hashval := b.hashval - HashAsAddCommGroup.op a
    invariant := by
      rw [b.invariant, instl.erase_toFinset]
      have h' : a ∈ instl.toFinset b.inner := by rw [← instl.toFinset_mem_iff] ; exact h
      rw [Finset.sum_erase_eq_sub h']
  }

instance : FinsetLike (HashCompanioned β ι) where
  insert := HashCompanioned.insert
  erase := HashCompanioned.erase

-- an easy lift
instance : LawfulFinsetLike (HashCompanioned β ι) where
  toFinset b := instl.toFinset b.inner
  toFinset_mem_iff a b := instl.toFinset_mem_iff a b.inner
  insert_toFinset a b h := instl.insert_toFinset a b.inner h
  erase_toFinset a b h := instl.erase_toFinset a b.inner h

instance [Hashable α] : Hashable (HashCompanioned β UInt64) where
  hash := HashCompanioned.hashval

instance : β ≃ HashCompanioned β ι where
  toFun b := { inner := b, hashval := (∑ a ∈ LawfulFinsetLike.toFinset b, insth.op a), invariant := rfl }
  invFun b := b.inner
  left_inv b := rfl
  right_inv b := by dsimp ; rcases b with ⟨i, h, inv⟩ ; subst h ; congr

-- `LawfulHashable` should be derivable from some weaker `BEq`,
-- not necessarily `DecidableEq`, especially there is no well-defined
-- `DecidableEq`
variable [DecidableEq β] [DecidableEq ι]

instance : DecidableEq (HashCompanioned β ι) :=
  fun a b =>
    let ⟨i1, h1, inv1⟩ := a
    let ⟨i2, h2, inv2⟩ := b
    let q : Decidable (i1 = i2) := inferInstance
    match q with
    | isTrue _ =>
      let qq : Decidable (h1 = h2) := inferInstance
      match qq with
      | isTrue _ => isTrue (by grind)
      | isFalse _ => isFalse (by grind)
    | isFalse _ => isFalse (by grind)

-- for `DecidableEq`, this is free
instance [Hashable α] : LawfulHashable (HashCompanioned β UInt64) :=
  inferInstance

end HashCompanioned

end Veil
