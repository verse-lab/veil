import Std
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Veil.Frontend.DSL.State.Interface

namespace Veil

/-! ## Generalised Sets and Total Maps -/

section FinsetLike

class FinsetLike (β : Type v) [Membership α β] where
  insert : (a : α) → (b : β) → a ∉ b → β
  erase : (a : α) → (b : β) → a ∈ b → β

class LawfulFinsetLike /- (α : outParam (Type u)) -/ (β : Type v)
  [Membership α β] [inst : FinsetLike β] [DecidableEq α] where
  toFinset : β → Finset α
  toFinset_mem_iff : ∀ (a : α) (b : β), a ∈ b ↔ a ∈ toFinset b
  insert_toFinset :
    ∀ (a : α) (b : β) (h : a ∉ b), toFinset (inst.insert a b h) = insert a (toFinset b)
  erase_toFinset :
    ∀ (a : α) (b : β) (h : a ∈ b), toFinset (inst.erase a b h) = (toFinset b).erase a

section DerivedOperations

variable {α : Type u} {β : Type v}
  [instm : Membership α β] [inst : FinsetLike β]
  [instdm : DecidableRel instm.mem]

@[specialize]
def FinsetLike.update (a : α) (in?' : Bool) (mp : β) : β :=
  if in? : a ∈ mp then
    if !in?' then inst.erase a mp in? else mp
  else
    if in?' then inst.insert a mp in? else mp

-- CHECK there are two ways of implementation: (1) `fold` and (2) `let mut` with loop.
-- which is faster? do both use the object linearly?
-- CHECK will typeclass affect things like reference counting?
def FinsetLike.batchUpdate (as : List α) (v : α → Bool) (mp : β) : β := Id.run do
  let mut res := mp
  for a in as do
    let in?' := v a
    if in? : a ∈ res then
      if !in?' then
        res := inst.erase a res in?
    else
      if in?' then
        res := inst.insert a res in?
  return res

-- a fairly "raw" proof about for-loop
theorem FinsetLike.batchUpdate_eq_foldl_update (as : List α) (v : α → Bool) (mp : β) :
  inst.batchUpdate as v mp = as.foldl (init := mp) fun acc a => inst.update a (v a) acc := by
  simp [batchUpdate, Id.run]
  conv =>
    enter [1]
    conv =>
      enter [3, p, r] ; simp [pure]
      conv => enter [2] ; intro h ; rw [← apply_ite ForInStep.yield]
      conv => enter [3] ; intro h ; rw [← apply_ite ForInStep.yield]
      repeat rw [← apply_dite ForInStep.yield]
      conv => enter [1] ; rw [← Id.run_pure (dite ..)] ; dsimp only [pure]
      rw [← Id.run_map _ ForInStep.yield]
    apply List.idRun_forIn_yield_eq_foldl
  congr ; ext b a ; simp [Id.run, update]

end DerivedOperations

end FinsetLike

section TotalMapLike

class TotalMapLike (α : outParam (Type u)) (β : outParam (Type v)) (γ : Type w) where
  get : γ → α → β
  insert : α → β → γ → γ

class LawfulTotalMapLike /- (α : outParam (Type u)) (β : outParam (Type v)) -/ (γ : Type w)
  [inst : TotalMapLike α β γ] [DecidableEq α] where
  insert_get : ∀ (a a' : α) (b : β) (mp : γ),
    inst.get (inst.insert a b mp) a' = if a = a' then b else inst.get mp a'

abbrev ArrayAsTotalMap (n : Nat) (β : Type v) := { mp : Array β // n = mp.size }

instance [Inhabited β] : Inhabited (ArrayAsTotalMap n β) :=
  ⟨⟨Array.replicate n default, Eq.symm Array.size_replicate⟩⟩

abbrev TotalHashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] :=
  { mp : Std.HashMap α β // ∀ a, a ∈ mp }

instance [FinEnum' α] [DecidableEq α] [Hashable α] [LawfulHashable α] [Inhabited β] : Inhabited (TotalHashMap α β) :=
  ⟨⟨Std.HashMap.ofList ((FinEnum'.allValues).map (fun a => (a, default))),
    by intro a ; rw [Std.HashMap.mem_ofList, List.map_map] ; unfold Function.comp ; simp [FinEnum'.complete]⟩⟩

abbrev TotalTreeMap (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare) :=
  { mp : Std.TreeMap α β cmp // ∀ a, a ∈ mp }

instance {cmp : α → α → Ordering} [FinEnum' α] [Std.LawfulEqCmp cmp] [Std.TransCmp cmp] [DecidableEq α] [Inhabited β] : Inhabited (TotalTreeMap α β cmp) :=
  ⟨⟨Std.TreeMap.ofList ((FinEnum'.allValues).map (fun a => (a, default))) cmp,
    by intro a ; rw [Std.TreeMap.mem_ofList, List.map_map] ; unfold Function.comp ; simp [FinEnum'.complete]⟩⟩

end TotalMapLike

section ConcreteUpdates

section FinsetLikeUpdates

variable {FieldDomain : List Type}
  [instd : DecidableEq α]
  [instm : Membership α β]
  [inst : FinsetLike β]
  [instl : LawfulFinsetLike β]
  [instdm : DecidableRel instm.mem]
  (equiv : IteratedProd FieldDomain ≃ α)
  (instfin : IteratedProd (FieldDomain.map FinEnum'))

def FieldRepresentation.FinsetLike.setSingle
  (fa : FieldUpdatePat FieldDomain)
  (v : CanonicalField FieldDomain Bool) (fc : β) :=
  inst.batchUpdate
    ((fa.footprintRaw instfin).cartesianProduct.map equiv) (v.uncurry ∘ equiv.symm) fc

def FieldRepresentation.FinsetLike.setSingle'
  (fa : FieldUpdatePat FieldDomain)
  (v : CanonicalField FieldDomain Bool) (fc : β) :=
  let vv := v.uncurry
  IteratedProd.foldMap fc (IteratedArrow.curry fun arg fc' =>
    inst.update (equiv arg) (vv arg) fc') (fa.footprintRaw instfin)

omit instd instl in
theorem FieldRepresentation.FinsetLike.setSingle_eq fa v (fc : β) :
  setSingle equiv instfin fa v fc = setSingle' equiv instfin fa v fc := by
  unfold setSingle setSingle'
  simp [FinsetLike.batchUpdate_eq_foldl_update, IteratedProd.foldMap_eq_cartesianProduct, IteratedArrow.uncurry_curry,
    List.foldl_map, Function.comp_apply]

instance instFinsetLikeAsFieldRep : FieldRepresentation FieldDomain Bool β :=
  FieldRepresentation.mkFromSingleSet
    (get := fun fc => IteratedArrow.curry (instm.mem fc ∘ equiv))
    (setSingle := FieldRepresentation.FinsetLike.setSingle' equiv instfin)

instance instFinsetLikeLawfulFieldRep : LawfulFieldRepresentation FieldDomain Bool β
    -- TODO this is awkward; synthesis fails here
    (instFinsetLikeAsFieldRep equiv instfin) where
  toLawfulFieldRepresentationSet :=
    LawfulFieldRepresentationSet.mkFromSingleSet ..
  get_set_idempotent := by open Classical in
    introv ; rcases fav with ⟨fa, v⟩
    simp +unfoldPartialApp [instFinsetLikeAsFieldRep, FieldRepresentation.mkFromSingleSet,
      CanonicalField.set, FieldRepresentation.set, FieldRepresentation.FinsetLike.setSingle',
      IteratedProd.foldMap_eq_cartesianProduct, FieldUpdateDescr.fieldUpdate, IteratedArrow.uncurry_curry,
      Function.comp]
    simp [← (FieldUpdatePat.footprint_match_iff instfin dec)]
    congr! 1 ; ext args ; rw [Bool.eq_iff_iff] ; simp
    -- `foldr` is more convenient for induction here
    rw [List.foldl_eq_foldr_reverse]
    conv => enter [2, 1] ; rw [← List.mem_reverse]
    generalize (fa.footprintRaw instfin).cartesianProduct.reverse = prods
    unfold FinsetLike.update
    generalize (v.uncurry) = vv
    generalize e : (fun x y => _) = ff
    induction prods with
    | nil => simp
    | cons p prods ih =>
      simp [ite_or, ← ih] ; clear ih
      generalize (List.foldr ..) = acc
      subst ff ; dsimp ; split_ifs <;> (try solve | grind)
      · subst p ; simp_all ; simp [instl.toFinset_mem_iff, instl.erase_toFinset]
      · simp [instl.toFinset_mem_iff, instl.erase_toFinset] ; simp_all
      · subst p ; simp_all ; simp [instl.toFinset_mem_iff, instl.insert_toFinset]
      · simp [instl.toFinset_mem_iff, instl.insert_toFinset] ; simp_all

end FinsetLikeUpdates

section TotalMapLikeUpdates

variable {FieldDomain : List Type} {FieldCodomain : Type}
  [instd : DecidableEq α]
  [inst : TotalMapLike α FieldCodomain γ]
  [instl : LawfulTotalMapLike γ]
  (equiv : IteratedProd FieldDomain ≃ α)
  (instfin : IteratedProd (FieldDomain.map FinEnum'))

def FieldRepresentation.TotalMapLike.setSingle'
  (fa : FieldUpdatePat FieldDomain)
  (v : CanonicalField FieldDomain FieldCodomain) (fc : γ) :=
  let vv := v.uncurry
  IteratedProd.foldMap fc (IteratedArrow.curry fun arg fc' =>
    inst.insert (equiv arg) (vv arg) fc') (fa.footprintRaw instfin)

instance instTotalMapLikeAsFieldRep : FieldRepresentation FieldDomain FieldCodomain γ :=
  FieldRepresentation.mkFromSingleSet
    (get := fun fc => IteratedArrow.curry (inst.get fc ∘ equiv))
    (setSingle := FieldRepresentation.TotalMapLike.setSingle' equiv instfin)

instance instTotalMapLikeLawfulFieldRep : LawfulFieldRepresentation FieldDomain FieldCodomain γ
    -- TODO this is awkward; synthesis fails here
    (instTotalMapLikeAsFieldRep equiv instfin) where
  toLawfulFieldRepresentationSet :=
    LawfulFieldRepresentationSet.mkFromSingleSet ..
  get_set_idempotent := by
    -- TODO this proof seems repetitive
    introv ; rcases fav with ⟨fa, v⟩
    open Classical in
    simp +unfoldPartialApp [instTotalMapLikeAsFieldRep, FieldRepresentation.mkFromSingleSet,
      CanonicalField.set, FieldRepresentation.set, FieldRepresentation.TotalMapLike.setSingle',
      IteratedProd.foldMap_eq_cartesianProduct, FieldUpdateDescr.fieldUpdate, IteratedArrow.uncurry_curry,
      Function.comp]
    simp [← (FieldUpdatePat.footprint_match_iff instfin dec)]
    congr! 1 ; ext args
    -- `foldr` is more convenient for induction here
    rw [List.foldl_eq_foldr_reverse]
    conv => enter [2, 1] ; rw [← List.mem_reverse]
    generalize (fa.footprintRaw instfin).cartesianProduct.reverse = prods
    generalize (v.uncurry) = vv
    induction prods with
    | nil => simp
    | cons p prods ih => simp [ite_or, ← ih, instl.insert_get] ; grind

end TotalMapLikeUpdates

end ConcreteUpdates

section ConcreteInstances

instance [BEq α] [Hashable α] : FinsetLike (Std.HashSet α) where
  insert a b _ := b.insert a
  erase a b _ := b.erase a

instance {cmp : α → α → Ordering} : FinsetLike (Std.TreeSet α cmp) where
  insert a b _ := b.insert a
  erase a b _ := b.erase a

instance [DecidableEq α] [Hashable α] : LawfulFinsetLike (Std.HashSet α) where
  toFinset b := List.toFinset b.toList
  toFinset_mem_iff a b := by simp
  insert_toFinset a b h := by
    ext a ; simp [FinsetLike.insert] ; aesop
  erase_toFinset a b h := by
    ext a ; simp [FinsetLike.erase] ; aesop

instance {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] [Std.TransCmp cmp]
  [DecidableEq α]   -- NOTE: this might be derived from `Std.LawfulEqCmp cmp`
  : LawfulFinsetLike (Std.TreeSet α cmp) where
  toFinset b := List.toFinset b.toList
  toFinset_mem_iff a b := by simp
  insert_toFinset a b h := by
    ext a ; simp [FinsetLike.insert] ; aesop
  erase_toFinset a b h := by
    ext a ; simp [FinsetLike.erase] ; aesop

instance : TotalMapLike (Fin n) β (ArrayAsTotalMap n β) where
  get mp a := mp.val[a.val]'(mp.property ▸ a.prop)
  insert a b mp := ⟨mp.val.set a.val b (mp.property ▸ a.prop),
    (Eq.symm (Array.size_set (xs := mp.val) (i := a.val) (mp.property ▸ a.prop))) ▸ mp.prop⟩

instance [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] : TotalMapLike α β (TotalHashMap α β) where
  get mp a := mp.val[a]'(mp.property a)
  insert a b mp := ⟨mp.val.insert a b,
    fun a => Std.HashMap.mem_insert.mpr (Or.inr (mp.property a))⟩

instance {cmp : α → α → Ordering} [Std.TransCmp cmp] : TotalMapLike α β (TotalTreeMap α β cmp) where
  get mp a := mp.val[a]'(mp.property a)
  insert a b mp := ⟨mp.val.insert a b,
    fun a => Std.TreeMap.mem_insert.mpr (Or.inr (mp.property a))⟩

instance : LawfulTotalMapLike (ArrayAsTotalMap n β) where
  insert_get a a' b mp := by
    dsimp [TotalMapLike.get, TotalMapLike.insert]
    simp [Array.getElem_set, Fin.val_inj]

variable {α : Type u}

instance [DecidableEq α] [Hashable α] [LawfulHashable α] : LawfulTotalMapLike (TotalHashMap α β) where
  insert_get a a' b mp := by
    dsimp [TotalMapLike.get, TotalMapLike.insert]
    rw [Std.HashMap.getElem_insert] ; simp ; congr

instance {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] [Std.TransCmp cmp]
  [DecidableEq α]   -- NOTE: this might be derived from `Std.LawfulEqCmp cmp`
  : LawfulTotalMapLike (TotalTreeMap α β cmp) where
  insert_get a a' b mp := by
    dsimp [TotalMapLike.get, TotalMapLike.insert]
    rw [Std.TreeMap.getElem_insert] ; simp ; congr

end ConcreteInstances

end Veil
