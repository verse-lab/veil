module

public import Std
public import Veil.Frontend.DSL.State.Concrete
public import Veil.Frontend.DSL.State.Data
public import Veil.Util.List
public import Veil.Util.ContainerDisplay
public import Std.Data.ExtTreeMap.Lemmas

@[expose] public section
namespace Veil
open Lean Std

/-!
`BEq` instances

We need `BEq` instance, as we sometimes hope to store them in `HashSet` or `HashMap`,
e.g., debugging, when we hope to store the complete information of a state `σᵣ`.
-/
-- Unlike Std's instances, these compare stored keys using `BEq` rather than `Ord`.
instance [Ord α] [BEq α]: BEq (Std.TreeSet α) where
  beq s1 s2 := s1.toArray == s2.toArray

instance [Ord α] [BEq α] [BEq β]: BEq (Std.TreeMap α β) where
  beq s1 s2 := s1.toArray == s2.toArray

-- FIXME: provide more reasonable `BEq` instances; same below
instance : BEq (CanonicalFieldWrapper FieldDomain FieldCodomain) where
  beq _ _ := true

/-!
`Hashable` instances

We always need `Hashable` instance. When we run the model checker,
we always store the hashable value of state representation `σᵣ` in `HashSet`.
-/
instance instHashableOfTreeSet [Hashable α] [Ord α]: Hashable (Std.TreeSet α) where
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

instance instHashableForFiniteFunction {α : Type u} {β : Type v}
  [Veil.Enumeration α] [Hashable β] : Hashable (α → β) where
  hash f :=
    let l := Veil.Enumeration.allValues (α := α)
    l.foldl (fun r a => mixHash r (hash (f a))) 7

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

instance [Ord α] [Std.TransOrd α] : Ord (Std.ExtTreeSet α) where
  compare s1 s2 := compare s1.toList s2.toList

instance instOrdExtTreeMap [Ord α] [Ord β] [Std.TransOrd α]
: Ord (Std.ExtTreeMap α β) where
  compare m1 m2 := compare m1.toList m2.toList

/-!
`DecidableEq` instances
-/

instance instDecidableMemList [DecidableEq α] (a : α) (l : List α) : Decidable (List.Mem a l) := List.instDecidableMemOfLawfulBEq a l

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
    · rw [Veil.List.mem_sublists]
      exact List.filter_sublist
    · apply Std.ExtTreeSet.ext_mem
      intro k
      rw [Std.ExtTreeSet.mem_ofList]
      grind

instance instEnumerationForExtTreeMap [Ord α]
  [DecidableEq α] [DecidableEq β]
  [Veil.Enumeration α] [Veil.Enumeration β]
  [Std.TransOrd α]
  [Std.LawfulEqOrd α]
  : Veil.Enumeration (Std.ExtTreeMap α β) where
  allValues :=
    let pairs := Veil.List.dedup (Veil.Enumeration.allValues (α := α × β))
    pairs.sublists.map (Std.ExtTreeMap.ofList ·)
  complete := by
    intro m
    rw [List.mem_map]
    let pairs := Veil.List.dedup (Veil.Enumeration.allValues (α := α × β))
    let l := pairs.filter (· ∈ m.toList)
    refine ⟨l, Veil.List.mem_sublists.mpr List.filter_sublist, ?_⟩
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    have hmem_toList : ∀ x ∈ l, x ∈ m.toList := fun x hx => by
      have := (List.mem_filter.mp hx).2; simp only [decide_eq_true_eq] at this; exact this
    have hl_nodup : l.Nodup := Veil.List.nodup_filter _ (Veil.List.nodup_dedup _)
    have hdistinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
      rw [List.pairwise_iff_forall_sublist]
      intro a b hab
      have ha := hmem_toList a (hab.subset (by simp))
      have hb := hmem_toList b (hab.subset (by simp))
      have hab_ne : a ≠ b := by
        intro heq; subst heq
        have : [a, a].Nodup := List.Sublist.nodup hab hl_nodup
        simp [List.nodup_cons] at this
      intro heq
      have hx' := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp ha
      have hy' := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hb
      have hget : m[a.1]? = m[b.1]? := Std.ExtTreeMap.getElem?_congr heq
      rw [hx', hy'] at hget
      exact hab_ne (Prod.ext (Std.LawfulEqCmp.eq_of_compare heq) (by simp at hget; exact hget))
    cases hm : m[k]? with
    | none =>
      rw [Std.ExtTreeMap.getElem?_ofList_of_contains_eq_false]
      simp only [List.contains_eq_any_beq, List.any_eq_false, List.mem_map, beq_iff_eq]
      intro p hp
      obtain ⟨q, hq, rfl⟩ := hp
      have hget := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp (hmem_toList q hq)
      intro heq; rw [heq, hget] at hm; grind
    | some v =>
      have hmem : (k, v) ∈ m.toList := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hm
      have hl_mem : (k, v) ∈ l := List.mem_filter.mpr ⟨Veil.List.mem_dedup.mpr (Veil.Enumeration.complete _), by simp only [decide_eq_true_eq]; exact hmem⟩
      rw [Std.ExtTreeMap.getElem?_ofList_of_mem (Std.ReflCmp.compare_self) hdistinct hl_mem]

/-!
`Inhabited` instances
-/

instance [Inhabited β] : Inhabited (Veil.CanonicalField α β) where
  default := Veil.IteratedArrow.curry fun _ => default

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

-- NOTE: Mathlib has this but Veil's dependencies do not
/-- A subtype displays as its value, e.g. a quorum as the set it is. -/
instance [ToJson α] {P : α → Prop} : ToJson (Subtype P) where
  toJson x := toJson x.val

/-! The concrete field representations below display their logical contents (the entries of the
map, the members of the set), as the finite functions they represent do, not their storage. -/

def ArrayAsFinmap.entries [inst : FinEncodable α] (m : ArrayAsFinmap α β) : Array (α × β) :=
  Array.ofFn fun i => (inst.equiv.symm i, m.val[i.val]'(m.property ▸ i.isLt))

def ArrayAsFinset.members [inst : FinEncodable α] (s : ArrayAsFinset α) : Array α :=
  Fin.foldl inst.card (init := #[]) fun out i =>
    if s.val[i.val]'(s.property ▸ i.isLt) then out.push (inst.equiv.symm i) else out

def BitVecAsFinmap.entries [inst : FinEncodable α] [FinEncodable β] [Inhabited β]
    (m : BitVecAsFinmap α β) : Array (α × β) :=
  Array.ofFn fun i =>
    let k := inst.equiv.symm i
    (k, FinmapLike.get m k)

instance [FinEncodable α] [Repr α] [Repr β] : Repr (ArrayAsFinmap α β) where
  reprPrec m _ := ContainerDisplay.mapFormat m.entries.toList

instance [FinEncodable α] [ToJson α] [ToJson β] : ToJson (ArrayAsFinmap α β) where
  toJson m := ContainerDisplay.mapJson m.entries

instance [FinEncodable α] [Repr α] : Repr (ArrayAsFinset α) where
  reprPrec s _ := ContainerDisplay.setFormat s.members.toList

instance [FinEncodable α] [ToJson α] : ToJson (ArrayAsFinset α) where
  toJson s := ContainerDisplay.setJson s.members

instance [FinEncodable α] [FinEncodable β] [Inhabited β] [Repr α] [Repr β] :
    Repr (BitVecAsFinmap α β) where
  reprPrec m _ := ContainerDisplay.mapFormat m.entries.toList

instance [FinEncodable α] [FinEncodable β] [Inhabited β] [ToJson α] [ToJson β] :
    ToJson (BitVecAsFinmap α β) where
  toJson m := ContainerDisplay.mapJson m.entries

/-- ToJson for curried finite functions: uncurry and use the product instance. -/
instance (priority := high) finFunctionToJsonCurry (α₁ : Type u) (α₂ : Type v) (β : Type w)
    [ToJson α₁] [Enumeration α₁] [ToJson α₂] [Enumeration α₂] [ToJson β]
    [inst : ToJson (α₁ × α₂ → β)] : ToJson (α₁ → α₂ → β) where
  toJson := fun f => inst.toJson (fun (x, y) => f x y)

/-- ToJson for finite functions: the map of all input/output pairs. A function of several arguments
is uncurried by `finFunctionToJsonCurry`, so its keys are tuples. -/
instance (priority := low) finFunctionToJson (α : Type u) (β : Type v)
    [ToJson α] [Enumeration α] [ToJson β] : ToJson (α → β) where
  toJson := fun f =>
    ContainerDisplay.mapJson ((Enumeration.allValues (α := α)).toArray.map fun a => (a, f a))

/-- ToJson for boolean predicates: the set of the elements where the predicate is true. -/
instance (priority := high) essentiallyFinSetToJson (α : Type u)
    [ToJson α] [Enumeration α] : ToJson (α → Bool) where
  toJson := fun f => ContainerDisplay.setJson <|
    (Enumeration.allValues (α := α)).foldl (fun out a => if f a then out.push a else out) #[]

instance jsonOfTreeSet [Ord α] [ToJson α] : ToJson (Std.TreeSet α) where
  toJson s := ContainerDisplay.setJson s.toArray

instance jsonOfTreeMap [Ord α] [ToJson α] [ToJson β] : ToJson (Std.TreeMap α β) where
  toJson m := ContainerDisplay.mapJson m.toArray

instance jsonOfExtTreeSet [Ord α] [ToJson α] [Std.TransOrd α] : ToJson (Std.ExtTreeSet α) where
  toJson s := ContainerDisplay.setJson s.toArray

instance jsonOfExtTreeMap [Ord α] [ToJson α] [ToJson β] [Std.TransOrd α] : ToJson (Std.ExtTreeMap α β) where
  toJson m := ContainerDisplay.mapJson m.toArray

instance jsonOfHashSet [BEq α] [Hashable α] [ToJson α] : ToJson (Std.HashSet α) where
  toJson s := ContainerDisplay.setJson s.toArray

instance jsonOfHashMap [BEq α] [Hashable α] [ToJson α] [ToJson β] : ToJson (Std.HashMap α β) where
  toJson m := ContainerDisplay.mapJson m.toArray


end Veil
