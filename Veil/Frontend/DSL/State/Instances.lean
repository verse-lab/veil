import Std
import Veil.Frontend.Std
import Veil.Frontend.DSL.State
import Veil.Frontend.DSL.State.Data

import Mathlib.Data.List.Sublists

namespace Veil
open Lean

/-
`BEq` instances

We need `BEq` instance, as we sometimes hope to store them in `HashSet` or `HashMap`,
e.g., debugging, when we hope to store the complete information of a state `σᵣ`.
-/
instance [Ord α] [BEq α]: BEq (Std.TreeSet α) where
  beq s1 s2 :=
    s1.toArray == s2.toArray

instance [Ord α] [BEq α] [BEq β]: BEq (Std.TreeMap α β) where
  beq s1 s2 :=
    s1.toArray == s2.toArray

instance [Ord α] [BEq α] [BEq β]: BEq (Veil.TotalTreeMap α β) where
  beq s1 s2 :=
    s1.val.toArray == s2.val.toArray

/-
  `DecidableEq` instances
-/
instance [Ord α] [DecidableEq α] : DecidableEq (Std.TreeSet α) :=
  fun s1 s2 => decidable_of_iff (s1.toArray = s2.toArray) (by sorry)

instance [Ord α] [DecidableEq α] [DecidableEq β] : DecidableEq (Std.TreeMap α β) :=
  fun s1 s2 => decidable_of_iff (s1.toArray = s2.toArray) (by sorry)

instance [Ord α] [DecidableEq α] [DecidableEq β] : DecidableEq (Veil.TotalTreeMap α β) :=
  fun s1 s2 => decidable_of_iff (s1.val.toArray = s2.val.toArray) (by sorry)

/--
`Hashable` instances

We always need `Hashable` instance. When we run the model checker,
we always store the hashable value of state representation `σᵣ` in `HashSet`.
-/
instance [Hashable α] [BEq α] [Ord α]: Hashable (Std.TreeSet α) where
  hash s := s.foldl (fun r a => mixHash r (hash a)) 7

instance [Ord α] [Hashable α] [Hashable β] : Hashable (Std.TreeMap α β) where
  hash s := s.foldl (fun r a b => mixHash r (mixHash (hash a) (hash b))) 7

/-
`Ord` instances

If we want to use `symmetric reduction` in model checking, we need `Ord` instances
to make the states comparable.
 -/
instance [Ord α] [Ord β] : Ord (α × β) where
  compare x y := match x, y with
    | (a, b), (a', b') => compare a a' |>.then (compare b b')

instance [Ord α] : Ord (Std.TreeSet α) where
  compare s1 s2 := compare s1.toArray s2.toArray

instance [Ord α] [Ord β] : Ord (Std.TreeMap α β) where
  compare s1 s2 := compare s1.toArray s2.toArray

instance [Ord α] [Ord β]: Ord (Veil.TotalTreeMap α β) where
  compare s1 s2 := compare s1.val.toArray s2.val.toArray


/-
  `Enumeration` instances

  If we want to execute transitions, we need to be able to enumerate
  (post-)states.

  FIXME: we probably need to switch to `ExtTreeSet` and `ExtTreeMap` to be able
  to prove `complete` for these instances.
-/

instance [DecidableEq α] [Ord α] [a : Enumeration α]: Enumeration (Std.TreeSet α) where
  allValues := (List.sublistsFast a.allValues).map (fun l => Std.TreeSet.ofList l)
  complete := by sorry
  decEq := inferInstance

instance [DecidableEq α] [DecidableEq β] [Ord α] [a : Enumeration α] [b : Enumeration β]
    : Enumeration (Std.TreeMap α β) where
  allValues :=
    let keys := a.allValues
    let vals := b.allValues
    ((List.sublistsFast keys).map (fun ks =>
      (allMappings ks vals).map (fun pairs => Std.TreeMap.ofList pairs))).flatten
  complete := by sorry
  decEq := inferInstance

instance [DecidableEq α] [DecidableEq β] [Ord α] [a : Enumeration α] [b : Enumeration β]
    : Enumeration (Veil.TotalTreeMap α β) where
  allValues :=
    let keys := a.allValues
    let vals := b.allValues
    (allMappings keys vals).map (fun pairs => ⟨Std.TreeMap.ofList pairs, by sorry⟩)
  complete := by sorry
  decEq := inferInstance

/-
`ToJson` instances
-/

instance : ToJson Bool where
  toJson := fun b => Json.bool b

instance : ToJson (Fin n) where
  toJson := fun f => toJson f.val

instance : ToJson Nat where
  toJson := fun n => Json.num n

instance (priority := low) jsonOfRepr [Repr α] : ToJson α where
  toJson := fun a => Json.str (toString (repr a))

/-- ToJson for curried finite functions: uncurry and use the product instance. -/
instance (priority := high) finFunctionToJsonCurry (α₁ : Type u) (α₂ : Type v) (β : Type w)
    [ToJson α₁] [FinEnum α₁] [ToJson α₂] [FinEnum α₂] [ToJson β]
    [inst : ToJson (α₁ × α₂ → β)] : ToJson (α₁ → α₂ → β) where
  toJson := fun f => inst.toJson (fun (x, y) => f x y)

/-- ToJson for finite functions: enumerate all input/output pairs as flat tuples.
    For a function `(a, b) -> c`, produces `[[a, b, c], ...]` rather than `[[[a, b], c], ...]`. -/
instance (priority := low) finFunctionToJson (α : Type u) (β : Type v)
    [ToJson α] [FinEnum α] [ToJson β] : ToJson (α → β) where
  toJson := fun f =>
    let l := FinEnum.toList α
    Json.arr <| l.toArray.map (fun a =>
      let keyJson := toJson a
      let valJson := toJson (f a)
      match keyJson with
      | Json.arr elems => Json.arr (elems.push valJson)
      | _ => Json.arr #[keyJson, valJson])

/-- ToJson for boolean predicates: show only the elements where the predicate is true. -/
instance (priority := high) essentiallyFinSetToJson (α : Type u)
    [ToJson α] [FinEnum α] : ToJson (α → Bool) where
  toJson := fun f => toJson (FinEnum.toList α |>.filter f)

instance jsonOfTuple [ToJson α] [ToJson β]: ToJson (α × β) where
  toJson := fun ⟨a, b⟩ => Json.arr #[toJson a, toJson b]

instance jsonOfList [ToJson α]: ToJson (List α) where
  toJson := fun xs => Json.arr (xs.toArray.map toJson)

instance jsonOfTreeSet [Ord α] [ToJson α] : ToJson (Std.TreeSet α) where
  toJson s := Json.arr <| s.toArray.map toJson

instance jsonOfTreeMap [Ord α] [ToJson α] [ToJson β] : ToJson (Std.TreeMap α β) where
  toJson m := Json.arr <| m.toArray.map (fun (k, v) => Json.arr #[toJson k, toJson v])

instance jsonOfTotalTreeMap [Ord α] [ToJson α] [ToJson β] : ToJson (Veil.TotalTreeMap α β) where
  toJson m := Json.arr <| m.val.toArray.map (fun (k, v) => Json.arr #[toJson k, toJson v])

end Veil
