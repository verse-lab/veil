module

public import Veil.Frontend.DSL.State.Concrete
public meta import Veil.Frontend.DSL.State.Concrete
public meta import Veil.Frontend.DSL.State.Types

/-! Full finite encodings for user-defined array index types. -/

open Veil

namespace VeilTest.Deriving.FinEncodable

-- Derivation needs neither Enumeration nor DecidableEq on the target or its
-- abstract field types. Verify constructor offsets and every decoder input.
inductive Index (α : Type u) (β : Type v) where
  | pair (a : α) (b : β)
  | single (a : α)
  | stop
deriving FinEncodable

example [FinEncodable α] [FinEncodable β] : FinEncodable (Index α β) := inferInstance

-- The forward path is the generated arithmetic match, even on an abstract x.
-- A proxy encoder would need to inspect x before reducing its Sum/Sigma values.
example [fa : FinEncodable α] [fb : FinEncodable β] (x : Index α β) :
    (FinEncodable.equiv x).val = match x with
      | .pair a b => (fa.equiv a).val * fb.card + (fb.equiv b).val
      | .single a => fa.card * fb.card + (fa.equiv a).val
      | .stop => fa.card * fb.card + (fa.card + 0) := rfl

#guard FinEncodable.card (Index (Fin 2) (Fin 3)) == 9
#guard (FinEncodable.equiv (Index.pair (1 : Fin 2) (2 : Fin 3))).val == 5
#guard (FinEncodable.equiv (Index.single (β := Fin 3) (1 : Fin 2))).val == 7
#guard (FinEncodable.equiv (Index.stop (α := Fin 2) (β := Fin 3))).val == 8

#eval do
  let enc := FinEncodable.equiv (α := Index (Fin 2) (Fin 3))
  for i in List.finRange 9 do
    assert! enc (enc.symm i) == i

example [FinEncodable α] [FinEncodable β] (x : Index α β) :
    FinEncodable.equiv.symm (FinEncodable.equiv x) = x := by simp

example [FinEncodable α] [FinEncodable β] (x : Index α β) :
    FinEncodable.equiv x =
      (FinEncodable.ofEquiv (veil_proxy_equiv% Index α β).symm).equiv x := by
  cases x <;> rfl

-- The actual consumer: read and update an array map using a newly derived key.
#eval do
  let key : Index (Fin 2) (Fin 3) := .pair 1 2
  let initial : ArrayAsFinmap (Index (Fin 2) (Fin 3)) Nat := default
  let updated := FinmapLike.insert key 42 initial
  assert! updated.val.size == 9
  assert! FinmapLike.get updated key == 42
  assert! FinmapLike.get updated (Index.single (β := Fin 3) (1 : Fin 2)) == 0

-- Product/Option fields compose directly from full field encodings.
structure Record (α : Type u) (β : Type v) where
  pair : α × β
  optional : Option α
deriving FinEncodable

example [FinEncodable α] [FinEncodable β] : FinEncodable (Record α β) := inferInstance
#guard FinEncodable.card (Record (Fin 2) (Fin 3)) == 18
#guard (FinEncodable.equiv (Record.mk ((1 : Fin 2), (2 : Fin 3)) (some 1))).val == 17

inductive Nested (α : Type u) (β : Type v) where
  | item (record : Record α β)
  | stop
deriving FinEncodable

#guard FinEncodable.card (Nested (Fin 2) (Fin 3)) == 19

-- Empty types, uninhabited constructor branches, and unused parameters.
inductive NoValues where
deriving FinEncodable

#guard FinEncodable.card NoValues == 0

structure NoFields where
deriving FinEncodable

#guard FinEncodable.card NoFields == 1

inductive Phantom (α : Type u) where
  | first | second
deriving FinEncodable

example (α : Type u) : FinEncodable (Phantom α) := inferInstance
#guard FinEncodable.card (Phantom Nat) == 2

inductive EmptyBranch where
  | impossible (x : Fin 0) (b : Bool)
  | only
deriving FinEncodable

#guard FinEncodable.card EmptyBranch == 1
#guard (FinEncodable.equiv EmptyBranch.only).val == 0

-- Implicit constructor fields and value parameters must retain their binders.
inductive ImplicitField (n : Nat) where
  | item {i : Fin n} (b : Bool)
  | stop
deriving FinEncodable

example (n : Nat) : FinEncodable (ImplicitField n) := inferInstance
#guard FinEncodable.card (ImplicitField 3) == 7
#guard (FinEncodable.equiv (ImplicitField.item (i := (2 : Fin 3)) true)).val == 5

-- Late deriving and nontrivial field types reuse existing proxy infrastructure.
inductive DependentFields where
  | item (n : Fin 3) (i : Fin (n.val + 1))
  | stop

deriving instance FinEncodable for DependentFields

#guard FinEncodable.card DependentFields == 7
#guard (FinEncodable.equiv DependentFields.stop).val == 6

inductive FunctionField (n : Nat) where
  | item (f : Fin n → Bool)
  | stop
deriving FinEncodable

#guard FinEncodable.card (FunctionField 2) == 5

-- Deriving does not use a custom target enumeration's order or duplicates.
inductive CustomEnumeration where
  | item (i : Fin 2)
  | stop
deriving DecidableEq

instance : Enumeration CustomEnumeration where
  allValues := [.stop, .item 1, .item 0, .stop]
  complete x := by cases x with
    | item i =>
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl <;> simp
    | stop => simp

deriving instance FinEncodable for CustomEnumeration

#guard FinEncodable.card CustomEnumeration == 3
#guard (FinEncodable.equiv (CustomEnumeration.item 1)).val == 1
#guard (FinEncodable.equiv CustomEnumeration.stop).val == 2

-- Sharing code must not mix the two classes' field encodings or cardinalities.
namespace DifferentEncodings

inductive Field where
  | first | second
deriving FinEncodable

instance : FinEncodableInjOnly Field where
  card := 3
  encode
    | .first => ⟨2, by decide⟩
    | .second => ⟨0, by decide⟩
  encode_inj := by
    intro a b h
    cases a <;> cases b <;> simp_all [Fin.ext_iff]

inductive Wrapped where
  | item (x : Field)
  | stop
deriving FinEncodable, FinEncodableInjOnly

#guard FinEncodable.card Wrapped == 3
#guard (FinEncodable.equiv (Wrapped.item .first)).val == 0
#guard (FinEncodable.equiv Wrapped.stop).val == 2
#guard FinEncodableInjOnly.card (κ := Wrapped) == 4
#guard (FinEncodableInjOnly.encode (Wrapped.item .first)).val == 2
#guard (FinEncodableInjOnly.encode Wrapped.stop).val == 3

end DifferentEncodings

-- Unsupported type shapes retain the proxy machinery's clear diagnostics.
/-- error: proxy equivalence: recursive inductive types are not supported (and are usually infinite) -/
#guard_msgs in
inductive Recursive where
  | stop
  | more (x : Recursive)
deriving FinEncodable

/-- error: proxy equivalence: inductive indices are not supported -/
#guard_msgs in
inductive Indexed : Bool → Type where
  | yes : Indexed true
  | no : Indexed false
deriving FinEncodable

end VeilTest.Deriving.FinEncodable
