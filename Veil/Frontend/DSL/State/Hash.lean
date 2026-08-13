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

def instEquiv : β ≃ HashCompanioned β ι op where
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

@[implicit_reducible]
def toFieldRepresentation (inst : FieldRepresentation FieldDomain FieldCodomain β)
  : FieldRepresentation FieldDomain FieldCodomain (HashCompanioned β ι op) where
  get cf := inst.get cf.inner
  set favs cf :=
    let res := inst.set favs cf.inner
    { inner := res, hashval := op res, invariant := rfl }

theorem toLawfulFieldRepresentation
  (inst : FieldRepresentation FieldDomain FieldCodomain β)
  (instl : LawfulFieldRepresentation FieldDomain FieldCodomain β inst)
  : LawfulFieldRepresentation FieldDomain FieldCodomain (HashCompanioned β ι op)
    (toFieldRepresentation _ inst) where
  set_nil := by intro fc ; cases fc ; simp +instances [toFieldRepresentation, instl.set_nil] ; grind
  set_append := by intro favs1 favs2 fc ; cases fc ; simp +instances [toFieldRepresentation, instl.set_append]
  get_set_idempotent := by intro dec fc favs ; cases fc ; simp +instances [toFieldRepresentation] ; apply instl.get_set_idempotent

end Simple

/-
-- FIXME: This needs more investigation
namespace IncrementalFinmapLike

variable {α : Type u} {β : Type v}
  [DecidableEq α] [inst : FinmapLike α Bool β] [instl : LawfulFinmapLike β]
  [AddCommGroup ι] [insth : HashAsAddCommGroup α ι]
  [Fintype α]

abbrev sumAsHash (inner : β) : ι :=
  ∑ a ∈ Finset.filter (fun a => inst.get inner a) Finset.univ, insth.op a

local macro "aop" : term => `(sumAsHash)

def insert' (a : α) (b : Bool) (c : HashCompanioned β ι aop) : HashCompanioned β ι aop :=
  let newInner := inst.insert a b c.inner
  { inner := newInner
    hashval := sumAsHash newInner
    invariant := rfl }

scoped instance : FinmapLike α Bool (HashCompanioned β ι aop) where
  get c a := inst.get c.inner a
  insert a b c := insert' a b c

scoped instance : LawfulFinmapLike (HashCompanioned β ι aop) where
  insert_get a a' b mp := by
    simp only [FinmapLike.get, FinmapLike.insert, insert']
    exact instl.insert_get a a' b mp.inner

scoped instance [Hashable α] : Hashable (HashCompanioned β UInt64 aop) where
  hash := HashCompanioned.hashval

end IncrementalFinmapLike

-/

end HashCompanioned

end Veil
