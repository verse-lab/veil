import Std
import Veil.Frontend.DSL.State.Concrete
import Veil.Frontend.DSL.State.Data
import Mathlib.Data.List.Sublists
import Std.Data.ExtTreeMap.Lemmas
namespace Veil
open Lean Std

/-!
`BEq` instances

We need `BEq` instance, as we sometimes hope to store them in `HashSet` or `HashMap`,
e.g., debugging, when we hope to store the complete information of a state `σᵣ`.
-/
instance [Ord α] [BEq α]: BEq (Std.TreeSet α) where
  beq s1 s2 := s1.toArray == s2.toArray

instance [Ord α] [BEq α] [BEq β]: BEq (Std.TreeMap α β) where
  beq s1 s2 := s1.toArray == s2.toArray

-- instance [Ord α] [BEq α] [BEq β]: BEq (Veil.TotalTreeMap α β) where
--   beq s1 s2 := s1.toArray == s2.toArray

-- FIXME: provide more reasonable `BEq` instances; same below
instance : BEq (CanonicalFieldWrapper FieldDomain FieldCodomain) where
  beq _ _ := true

/-!
`Hashable` instances

We always need `Hashable` instance. When we run the model checker,
we always store the hashable value of state representation `σᵣ` in `HashSet`.
-/
instance instHashableOfTreeSet [Hashable α] [BEq α] [Ord α]: Hashable (Std.TreeSet α) where
  hash s := s.foldl (fun r a => mixHash r (hash a)) 7

instance instHashableOfTreeMap [Ord α] [Hashable α] [Hashable β] : Hashable (Std.TreeMap α β) where
  hash s := s.foldl (fun r a b => mixHash r (mixHash (hash a) (hash b))) 7

instance instHashableOfExtTreeSet [Ord α] [Hashable α] [Std.TransOrd α]: Hashable (Std.ExtTreeSet α) where
  hash s := s.foldl (fun r a => mixHash r (hash a)) 7

instance instHashableOfExtTreeMap [Ord α] [Hashable α] [Hashable β] [Std.TransOrd α]
  : Hashable (Std.ExtTreeMap α β) where
  hash s := s.foldl (fun r a b => mixHash r (mixHash (hash a) (hash b))) 7

instance : Hashable (CanonicalFieldWrapper FieldDomain FieldCodomain) where
  hash _ := 13

deriving instance Hashable for Sum

/-!
`Ord` instances

If we want to use `symmetric reduction` in model checking, we need `Ord` instances
to make the states comparable.
 -/

attribute [instance] lexOrd

instance [Ord α] : Ord (Std.TreeSet α) where
  compare s1 s2 := compare s1.toArray s2.toArray

instance [Ord α] [Ord β] : Ord (Std.TreeMap α β) where
  compare s1 s2 := compare s1.toArray s2.toArray

-- instance [Ord α] [Ord β] : Ord (Veil.TotalTreeMap α β) where
--   compare s1 s2 := compare s1.toArray s2.toArray

instance [Ord α] [Std.TransOrd α] : Ord (Std.ExtTreeSet α) where
  compare s1 s2 := compare s1.toList s2.toList

instance instOrdExtTreeMap [Ord α] [Ord β] [Std.TransOrd α]
: Ord (Std.ExtTreeMap α β) where
  compare m1 m2 := compare m1.toList m2.toList

/-!
`DecidableEq` instances
-/

instance instDecidableEqExtTreeSet [Ord α] [DecidableEq α] [Std.TransOrd α]
  : DecidableEq (Std.ExtTreeSet α) := fun t₁ t₂ =>
  decidable_of_iff (t₁.toList = t₂.toList) Std.ExtTreeSet.toList_inj

instance instDecidableEqExtTreeMap [Ord α] [DecidableEq α] [DecidableEq β]
  [Std.TransOrd α] : DecidableEq (Std.ExtTreeMap α β) := fun m1 m2 =>
  decidable_of_iff (m1.toList = m2.toList) Std.ExtTreeMap.toList_inj

/-!
`Std.TransOrd` and `Std.LawfulEqOrd` instances
-/

instance instTransOrdExtTreeSet [Ord α] [Std.TransOrd α]
  : Std.TransOrd (Std.ExtTreeSet α) where
  eq_swap := by
    intro s1 s2
    dsimp [compare]
    exact Std.OrientedCmp.eq_swap
  isLE_trans := by
    intro s1 s2 s3 h1 h2
    dsimp [compare] at *
    apply Std.TransCmp.isLE_trans h1 h2

instance instTransOrdExtTreeMap [Ord α] [Ord β] [Std.TransOrd α] [Std.TransOrd β]
  : Std.TransOrd (Std.ExtTreeMap α β) where
  eq_swap := by
    intro m1 m2
    show compare m1 m2 = (compare m2 m1).swap
    show compare m1.toList m2.toList = (compare m2.toList m1.toList).swap
    exact Std.OrientedCmp.eq_swap
  isLE_trans := by
    intro m1 m2 m3 h1 h2
    -- Similarly for transitivity
    show (compare m1 m3).isLE = true
    show (compare m1.toList m3.toList).isLE = true
    have h1' : (compare m1.toList m2.toList).isLE = true := h1
    have h2' : (compare m2.toList m3.toList).isLE = true := h2
    exact Std.TransCmp.isLE_trans h1' h2'


instance instLawfulOrdExtTreeSet [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
  : Std.LawfulEqOrd (Std.ExtTreeSet α) where
  compare_self := by
    intro s
    dsimp [compare]
    exact Std.ReflCmp.compare_self
  eq_of_compare := by
    intro s1 s2 h
    dsimp [compare] at h
    apply Std.ExtTreeSet.ext_mem
    intro a
    have : s1.toList = s2.toList := Std.LawfulEqCmp.eq_of_compare h
    rw [← Std.ExtTreeSet.mem_toList, this, Std.ExtTreeSet.mem_toList]


instance instLawfulOrdExtTreeMap
  [Ord α] [Ord β]
  [Std.TransOrd α]
  [Std.LawfulEqOrd α]
  [Std.LawfulEqOrd β]
  : Std.LawfulEqOrd (Std.ExtTreeMap α β) where
  compare_self := by
    intro m
    show compare m m = .eq
    show compare m.toList m.toList = .eq
    exact Std.ReflCmp.compare_self
  eq_of_compare := by
    intro m1 m2 h
    have h' : compare m1.toList m2.toList = .eq := h
    have : m1.toList = m2.toList := @Std.LawfulEqCmp.eq_of_compare _ compare _ _ _ h'
    exact Std.ExtTreeMap.toList_inj.mp this

/-!
  `Enumeration` instances

  If we want to execute transitions, we need to be able to enumerate
  (post-)states.

  `complete` can only be proved for `ExtTreeSet` and `ExtTreeMap` if
  the comparison between elements is done with `=`.
-/

instance instEnumerationForExtTreeSet [Ord α] [Veil.Enumeration α] [DecidableEq α]
  [Std.TransOrd α] [Std.LawfulEqOrd α]
  : Veil.Enumeration (Std.ExtTreeSet α) where
  allValues := (Veil.Enumeration.allValues (α := α)).sublists.map (Std.ExtTreeSet.ofList ·)
  complete := by
    intro s
    rw [List.mem_map]
    let l := Veil.Enumeration.allValues.filter (· ∈ s)
    exists l
    constructor
    · rw [List.mem_sublists]
      exact List.filter_sublist
    · apply Std.ExtTreeSet.ext_mem
      intro k
      rw [Std.ExtTreeSet.mem_ofList]
      grind

instance instEnumerationForExtTreeMap [Ord α] [Ord β]
  [DecidableEq α] [DecidableEq β]
  [Veil.Enumeration α] [Veil.Enumeration β]
  [Std.TransOrd α] [Std.TransOrd β]
  [Std.LawfulEqOrd α] [Std.LawfulEqOrd β]
  : Veil.Enumeration (Std.ExtTreeMap α β) where
  allValues :=
    let pairs := Veil.Enumeration.allValues (α := α × β)
    pairs.sublists.map (Std.ExtTreeMap.ofList ·)
  complete := by
      intro m
      rw [List.mem_map]
      let pairs := Veil.Enumeration.allValues (α := α × β)
      let l := pairs.filter fun ⟨k, v⟩ => k ∈ m ∧ m.get? k = some v
      exists l
      constructor
      · rw [List.mem_sublists]
        exact List.filter_sublist
      · sorry

/-
instance [DecidableEq α] [Ord α] [a : Enumeration α]: Enumeration (Std.TreeSet α) where
  allValues := (List.sublistsFast a.allValues).map (fun l => Std.TreeSet.ofList l)
  complete := by sorry

instance [DecidableEq α] [DecidableEq β] [Ord α] [a : Enumeration α] [b : Enumeration β]
    : Enumeration (Std.TreeMap α β) where
  allValues :=
    let keys := a.allValues
    let vals := b.allValues
    ((List.sublistsFast keys).map (fun ks =>
      (allMappings ks vals).map (fun pairs => Std.TreeMap.ofList pairs))).flatten
  complete := by sorry

instance [DecidableEq α] [DecidableEq β] [Ord α] [a : Enumeration α] [b : Enumeration β]
    : Enumeration (Veil.TotalTreeMap α β) where
  allValues :=
    let keys := a.allValues
    let vals := b.allValues
    (allMappings keys vals).map (fun pairs => ⟨Std.TreeMap.ofList pairs, by sorry⟩)
  complete := by sorry
-/

/-!
`Inhabited` instances
-/

instance instInhabitedForExtTreeSet [Inhabited α] [Ord α]: Inhabited (Std.ExtTreeSet α) :=
  ⟨Std.ExtTreeSet.empty⟩

/-!
`ToJson` instances
-/

-- We make these high priority so typeclass inference doesn't get into strange
-- loops trying to figure them out via the lifting of `ToJson` for fields
attribute [instance high] instToJsonBool
attribute [instance high] instToJsonNat
attribute [instance high] instToJsonInt
attribute [instance high] instToJsonString

instance : ToJson (Fin n) where
  toJson := fun f => toJson f.val

instance (priority := low) reprOfUnrepresentable : Repr α where
  reprPrec _ _ := "<unrepresentable>"

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

instance jsonOfTreeSet [Ord α] [ToJson α] : ToJson (Std.TreeSet α) where
  toJson s := Json.arr <| s.toArray.map toJson

instance jsonOfTreeMap [Ord α] [ToJson α] [ToJson β] : ToJson (Std.TreeMap α β) where
  toJson m := Json.arr <| m.toArray.map (fun (k, v) => Json.arr #[toJson k, toJson v])

-- instance jsonOfTotalTreeMap [Ord α] [ToJson α] [ToJson β] : ToJson (Veil.TotalTreeMap α β) where
--   toJson m := Json.arr <| m.toArray.map (fun (k, v) => Json.arr #[toJson k, toJson v])

instance jsonOfExtTreeSet [Ord α] [ToJson α] [Std.TransOrd α] : ToJson (Std.ExtTreeSet α) where
  toJson s := Json.arr <| s.toList.toArray.map toJson

instance jsonOfExtTreeMap [Ord α] [ToJson α] [ToJson β] [Std.TransOrd α] : ToJson (Std.ExtTreeMap α β) where
  toJson m := Json.arr <| m.toList.toArray.map (fun (k, v) => Json.arr #[toJson k, toJson v])


end Veil
