import Mathlib.Data.UInt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Veil.Frontend.DSL.State.Concrete

namespace Veil

class HashAsAddCommGroup (α : Type u) (ι : Type w) where
  op : α → ι

instance [Hashable α] : HashAsAddCommGroup α UInt64 where
  op := hash

-- "lifting" a data structure to store its hash alongside;
-- if the hash value can be efficiently updated upon insert/erase,
-- then we can maintain the hash value *incrementally*

-- CAVEAT: `β × UInt64` is not enough; it does not carry any invariant
-- that is required for proving the `LawfulHashable` of the whole thing;
-- to maintain this invariant, need `LawfulFinsetLike`
-- CAVEAT: the update of `hashval` depends on the membership, so need to
-- do something about this
structure HashCompanioned (β : Type v) (ι : Type w)
  -- [DecidableEq α] [Membership α β]
  -- [FinsetLike β] [LawfulFinsetLike β]
  (op : β → ι) where
  inner : β
  hashval : ι
  invariant : hashval = op inner

namespace HashCompanioned

variable {β : Type v} {ι : Type w} (op : β → ι)

instance [Membership α β] : Membership α (HashCompanioned β ι op) where
  mem b a := a ∈ b.inner

instance [BEq β] [BEq ι] : BEq (HashCompanioned β ι op) where
  beq b1 b2 := b1.inner == b2.inner && b1.hashval == b2.hashval

instance [Lean.ToJson β] [Lean.ToJson ι] : Lean.ToJson (HashCompanioned β ι op) where
  toJson b := Lean.toJson b.inner

instance [Inhabited β] : Inhabited (HashCompanioned β ι op) where
  default := { inner := default, hashval := op default, invariant := rfl }

instance : β ≃ HashCompanioned β ι op where
  toFun b := { inner := b, hashval := op b, invariant := rfl }
  invFun b := b.inner
  left_inv b := rfl
  right_inv b := by dsimp ; rcases b with ⟨i, h, inv⟩ ; subst h ; congr

namespace Simple

omit ι β op
variable {β ι : Type} (op : β → ι) {FieldDomain : List Type} {FieldCodomain : Type}

omit op in
scoped instance [Hashable β] : Hashable (HashCompanioned β UInt64 hash) where
  hash := HashCompanioned.hashval

def toFieldRepresentation (inst : FieldRepresentation FieldDomain FieldCodomain β)
  : FieldRepresentation FieldDomain FieldCodomain (HashCompanioned β ι op) where
  get cf := inst.get cf.inner
  set favs cf :=
    let res := inst.set favs cf.inner
    { inner := res, hashval := op res, invariant := rfl }

def toLawfulFieldRepresentation
  (inst : FieldRepresentation FieldDomain FieldCodomain β)
  (instl : LawfulFieldRepresentation FieldDomain FieldCodomain β inst)
  : LawfulFieldRepresentation FieldDomain FieldCodomain (HashCompanioned β ι op)
    (toFieldRepresentation _ inst) where
  set_nil := by intro fc ; cases fc ; simp [toFieldRepresentation, instl.set_nil] ; grind
  set_append := by intro favs1 favs2 fc ; cases fc ; simp [toFieldRepresentation, instl.set_append]
  get_set_idempotent := by intro dec fc favs ; cases fc ; simp [toFieldRepresentation] ; apply instl.get_set_idempotent

end Simple

namespace IncrementalFinsetLike

-- TODO maybe adapt this to map structures as well, later

variable {α : Type u}
  [DecidableEq α] [Membership α β]
  [instf : FinsetLike β] [instl : LawfulFinsetLike β]
  [AddCommGroup ι] [insth : HashAsAddCommGroup α ι]

abbrev sumAsHash (inner : β) : ι :=
  ∑ a ∈ LawfulFinsetLike.toFinset inner, insth.op a

local macro "aop" : term => `(sumAsHash)

def insert (a : α) (b : HashCompanioned β ι aop) (h : a ∉ b) : HashCompanioned β ι aop :=
  { inner := FinsetLike.insert a b.inner h
    hashval := HashAsAddCommGroup.op a + b.hashval
    invariant := by
      rw [sumAsHash, b.invariant, instl.insert_toFinset]
      have h' : a ∉ instl.toFinset b.inner := by rw [← instl.toFinset_mem_iff] ; exact h
      rw [Finset.sum_insert' (M := ι) h']
  }

def erase (a : α) (b : HashCompanioned β ι aop) (h : a ∈ b) : HashCompanioned β ι aop :=
  { inner := FinsetLike.erase a b.inner h
    hashval := b.hashval - HashAsAddCommGroup.op a
    invariant := by
      rw [sumAsHash, b.invariant, instl.erase_toFinset]
      have h' : a ∈ instl.toFinset b.inner := by rw [← instl.toFinset_mem_iff] ; exact h
      rw [Finset.sum_erase_eq_sub h']
  }

scoped instance : FinsetLike (HashCompanioned β ι aop) where
  insert := insert
  erase := erase

scoped instance : LawfulFinsetLike (HashCompanioned β ι aop) where
  toFinset b := instl.toFinset b.inner
  toFinset_mem_iff a b := instl.toFinset_mem_iff a b.inner
  insert_toFinset a b h := instl.insert_toFinset a b.inner h
  erase_toFinset a b h := instl.erase_toFinset a b.inner h

scoped instance [Hashable α] : Hashable (HashCompanioned β UInt64 aop) where
  hash := HashCompanioned.hashval

end IncrementalFinsetLike

end HashCompanioned

end Veil
