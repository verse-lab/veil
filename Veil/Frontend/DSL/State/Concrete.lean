import Std
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Veil.Frontend.DSL.State.Interface
import Veil.Frontend.DSL.Module.Names

namespace Veil

/-! ## Utilities -/

abbrev Nat.bitLength (n : Nat) : Nat := Nat.log2 (n - 1) + 1

theorem Nat.bitLength_range {n : Nat} : n ≤ 2 ^ (Nat.bitLength n) :=
  if h : n = 0
  then (by subst n ; decide)
  else if h' : n = 1
    then (by subst n ; decide)
    else (by
      unfold Nat.bitLength
      rw [← Nat.log2_two_mul]
      on_goal 2=> omega
      set k := (2 * (n - 1)).log2
      have hh := @Nat.log2_eq_iff (2 * (n - 1)) k (by omega) |>.mp rfl |>.right
      simp [Nat.pow_succ] at hh ; rw [Nat.mul_comm, Nat.mul_lt_mul_right] at hh
      on_goal 2=> decide
      omega
    )

abbrev Fin.minCast (m : Nat) (h : m ≠ 0) (i : Fin n) : Fin m :=
  ⟨Nat.min i.val (m - 1),
    Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_one_lt h)⟩

theorem BitVec.shiftLeft_then_ushiftRight_eq (n : BitVec w) (m : Nat) :
  w + m ≤ w' →
  ((BitVec.setWidth w' n) <<< m) >>> m = BitVec.setWidth w' n := by
  intro h ; ext ; simp ; grind

theorem BitVec.xor_getself_iff {x y : BitVec w} :
  x ^^^ y = x ↔ y = BitVec.zero w := by
  constructor
  · intro h ; rewrite (occs := .neg [1]) [← @BitVec.xor_zero _ x] at h
    rw [BitVec.xor_right_inj] at h ; exact h
  · intro h ; subst y ; simp

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

instance [Enumeration α] [DecidableEq α] [Hashable α] [LawfulHashable α] [Inhabited β] : Inhabited (TotalHashMap α β) :=
  ⟨⟨Std.HashMap.ofList ((Enumeration.allValues).map (fun a => (a, default))),
    by intro a ; rw [Std.HashMap.mem_ofList, List.map_map] ; unfold Function.comp ; simp [Enumeration.complete]⟩⟩

abbrev TotalTreeMap (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare) :=
  { mp : Std.TreeMap α β cmp // ∀ a, a ∈ mp }

instance {cmp : α → α → Ordering} [Enumeration α] [Std.LawfulEqCmp cmp] [Std.TransCmp cmp] [DecidableEq α] [Inhabited β] : Inhabited (TotalTreeMap α β cmp) :=
  ⟨⟨Std.TreeMap.ofList ((Enumeration.allValues).map (fun a => (a, default))) cmp,
    by intro a ; rw [Std.TreeMap.mem_ofList, List.map_map] ; unfold Function.comp ; simp [Enumeration.complete]⟩⟩

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
  (instfin : IteratedProd (FieldDomain.map Enumeration))

def FieldRepresentation.FinsetLike.get (fc : β) : CanonicalField FieldDomain Bool :=
  IteratedArrow.curry (instm.mem fc ∘ equiv)

def FieldRepresentation.FinsetLike.setSingle
  (fa : FieldUpdatePat FieldDomain)
  (v : CanonicalField FieldDomain Bool) (fc : β) :=
  inst.batchUpdate
    ((fa.footprintRaw instfin).cartesianProduct.map equiv) (v.uncurry ∘ equiv.symm) fc

def FieldRepresentation.FinsetLike.setSingle'Core
  (v : CanonicalField FieldDomain Bool) (fc : β)
  (footprint : IteratedProd (FieldDomain.map (fun {ty} => Unit → List ty))) :=
  let vv := v.uncurry
  IteratedProd.foldMap fc (IteratedArrow.curry fun arg fc' =>
    inst.update (equiv arg) (vv arg) fc') footprint

def FieldRepresentation.FinsetLike.setSingle'
  (fa : FieldUpdatePat FieldDomain)
  (v : CanonicalField FieldDomain Bool) (fc : β) :=
  delta% FieldRepresentation.FinsetLike.setSingle'Core equiv v fc (fa.footprintRaw instfin)

omit instd instl in
theorem FieldRepresentation.FinsetLike.setSingle_eq fa v (fc : β) :
  setSingle equiv instfin fa v fc = setSingle' equiv instfin fa v fc := by
  unfold setSingle setSingle'
  simp [FinsetLike.batchUpdate_eq_foldl_update, IteratedProd.foldMap_eq_cartesianProduct, IteratedArrow.uncurry_curry,
    List.foldl_map, Function.comp_apply]

instance instFinsetLikeAsFieldRep : FieldRepresentation FieldDomain Bool β :=
  FieldRepresentation.mkFromSingleSet
    (get := delta% FieldRepresentation.FinsetLike.get equiv)
    (setSingle := FieldRepresentation.FinsetLike.setSingle' equiv instfin)

theorem FieldRepresentation.FinsetLike.get_set_for_validFootprint
  (dec : IteratedProd (List.map DecidableEq FieldDomain)) (fc : β)
  (fa : FieldUpdatePat FieldDomain) (v : CanonicalField FieldDomain Bool)
  (footprint : _) (h : fa.validFootprint footprint) :
  get equiv (setSingle'Core equiv v fc footprint) =
    CanonicalField.set dec [(fa, v)] (get equiv fc) := by classical
  simp +unfoldPartialApp [get, setSingle'Core, CanonicalField.set,
    IteratedProd.foldMap_eq_cartesianProduct, FieldUpdateDescr.fieldUpdate, IteratedArrow.uncurry_curry,
    Function.comp]
  simp [← (FieldUpdatePat.footprint_match_iff_when_valid dec h)]
  congr! 1 ; ext args ; rw [Bool.eq_iff_iff] ; simp
  -- `foldr` is more convenient for induction here
  rw [List.foldl_eq_foldr_reverse]
  conv => enter [2, 1] ; rw [← List.mem_reverse]
  generalize footprint.cartesianProduct.reverse = prods
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

instance instFinsetLikeLawfulFieldRep : LawfulFieldRepresentation FieldDomain Bool β
    -- TODO this is awkward; synthesis fails here
    (instFinsetLikeAsFieldRep equiv instfin) where
  toLawfulFieldRepresentationSet :=
    LawfulFieldRepresentationSet.mkFromSingleSet ..
  get_set_idempotent := by
    introv
    apply FieldRepresentation.FinsetLike.get_set_for_validFootprint
    apply FieldUpdatePat.footprintRaw_valid

end FinsetLikeUpdates

/-- A wrapper around `CanonicalField` to indicate that this field is used
as part of a hybrid finset-like representation. It might have special
`BEq` and `Hashable` instances. -/
structure CanonicalFieldWrapper (FieldDomain : List Type) (FieldCodomain : Type) where
  inner : CanonicalField FieldDomain FieldCodomain

inductive HybridFieldType (α : Type u) (FieldDomain : List Type) (FieldCodomain : Type) where
  | canonical (cf : CanonicalFieldWrapper FieldDomain FieldCodomain)
  | concrete (fc : α)

instance [BEq (CanonicalFieldWrapper FieldDomain FieldCodomain)] [BEq α] :
  BEq (HybridFieldType α FieldDomain FieldCodomain) where
  beq
    | HybridFieldType.canonical cf1, HybridFieldType.canonical cf2 =>
      cf1 == cf2
    | HybridFieldType.concrete fc1, HybridFieldType.concrete fc2 =>
      fc1 == fc2
    | _, _ => false

instance [Hashable (CanonicalFieldWrapper FieldDomain FieldCodomain)] [Hashable α] :
  Hashable (HybridFieldType α FieldDomain FieldCodomain) where
  hash
    | HybridFieldType.canonical cf => mixHash 17 (hash cf)
    | HybridFieldType.concrete fc => mixHash 19 (hash fc)

-- For `Inhabited`, only provide for the `concrete` case
instance [Inhabited α] : Inhabited (HybridFieldType α FieldDomain FieldCodomain) :=
  ⟨HybridFieldType.concrete default⟩

namespace NotNecessarilyFinsetLikeUpdates

variable {FieldDomain : List Type}
  [instd : DecidableEq α]
  [instm : Membership α β]
  [inst : FinsetLike β]
  [instl : LawfulFinsetLike β]
  [instdm : DecidableRel instm.mem]
  (equiv : IteratedProd FieldDomain ≃ α)
  (instfin : IteratedProd (FieldDomain.map (OptionalTC ∘ Enumeration)))
  (instdeceq : IteratedProd (FieldDomain.map DecidableEq))

abbrev HybridFinsetLike (β) (FieldDomain : List Type) := HybridFieldType β FieldDomain Bool

def HybridFinsetLike.get : HybridFinsetLike β FieldDomain → CanonicalField FieldDomain Bool
  | .canonical cf => cf.inner
  | .concrete fc => delta% FieldRepresentation.FinsetLike.get equiv fc

def HybridFinsetLike.setSingle
  (fa : FieldUpdatePat FieldDomain)
  (v : CanonicalField FieldDomain Bool) (fc : HybridFinsetLike β FieldDomain)
  : HybridFinsetLike β FieldDomain :=
  match fc with
  | .canonical cf => .canonical <| CanonicalFieldWrapper.mk <| CanonicalField.set instdeceq [(fa, v)] cf.inner
  | .concrete fc' =>
    match fa.footprintRestricted instfin with
    | none => .canonical <| CanonicalFieldWrapper.mk <| CanonicalField.set instdeceq [(fa, v)]
      <| FieldRepresentation.FinsetLike.get equiv fc'
    | some footprint => .concrete <|
      FieldRepresentation.FinsetLike.setSingle'Core equiv v fc' footprint

instance instHybridFinsetLikeAsFieldRep : FieldRepresentation FieldDomain Bool
  (HybridFinsetLike β FieldDomain) :=
  FieldRepresentation.mkFromSingleSet
    (get := delta% HybridFinsetLike.get equiv)
    (setSingle := HybridFinsetLike.setSingle equiv instfin instdeceq)

instance instHybridFinsetLikeLawfulFieldRep : LawfulFieldRepresentation FieldDomain Bool
    (HybridFinsetLike β FieldDomain)
    -- TODO this is awkward; synthesis fails here
    (instHybridFinsetLikeAsFieldRep equiv instfin instdeceq) where
  toLawfulFieldRepresentationSet :=
    LawfulFieldRepresentationSet.mkFromSingleSet ..
  get_set_idempotent := by open Classical in
    introv ; rcases fav with ⟨fa, v⟩
    simp +unfoldPartialApp [instHybridFinsetLikeAsFieldRep, FieldRepresentation.mkFromSingleSet,
      FieldRepresentation.set, HybridFinsetLike.setSingle]
    rcases fc with cf | fc <;> dsimp only
    · congr ; apply IteratedProd.map_DecidableEq_eq
    · rcases h : FieldUpdatePat.footprintRestricted instfin fa with _ | footprint <;> dsimp only
      · congr ; apply IteratedProd.map_DecidableEq_eq
      · apply FieldRepresentation.FinsetLike.get_set_for_validFootprint
        apply FieldUpdatePat.footprintRestricted_valid
        apply h

end NotNecessarilyFinsetLikeUpdates

section TotalMapLikeUpdates

variable {FieldDomain : List Type} {FieldCodomain : Type}
  [instd : DecidableEq α]
  [inst : TotalMapLike α FieldCodomain γ]
  [instl : LawfulTotalMapLike γ]
  (equiv : IteratedProd FieldDomain ≃ α)
  (instfin : IteratedProd (FieldDomain.map Enumeration))

def FieldRepresentation.TotalMapLike.get (fc : γ) : CanonicalField FieldDomain FieldCodomain :=
  IteratedArrow.curry (inst.get fc ∘ equiv)

def FieldRepresentation.TotalMapLike.setSingle'Core
  (v : CanonicalField FieldDomain FieldCodomain) (fc : γ)
  (footprint : IteratedProd (FieldDomain.map (fun {ty} => Unit → List ty))) :=
  let vv := v.uncurry
  IteratedProd.foldMap fc (IteratedArrow.curry fun arg fc' =>
    inst.insert (equiv arg) (vv arg) fc') footprint

def FieldRepresentation.TotalMapLike.setSingle'
  (fa : FieldUpdatePat FieldDomain)
  (v : CanonicalField FieldDomain FieldCodomain) (fc : γ) :=
  delta% FieldRepresentation.TotalMapLike.setSingle'Core equiv v fc (fa.footprintRaw instfin)

instance instTotalMapLikeAsFieldRep : FieldRepresentation FieldDomain FieldCodomain γ :=
  FieldRepresentation.mkFromSingleSet
    (get := delta% FieldRepresentation.TotalMapLike.get equiv)
    (setSingle := FieldRepresentation.TotalMapLike.setSingle' equiv instfin)

theorem FieldRepresentation.TotalMapLike.get_set_for_validFootprint
  (dec : IteratedProd (List.map DecidableEq FieldDomain)) (fc : γ)
  (fa : FieldUpdatePat FieldDomain) (v : CanonicalField FieldDomain FieldCodomain)
  (footprint : _) (h : fa.validFootprint footprint) :
  get equiv (setSingle'Core equiv v fc footprint) =
    CanonicalField.set dec [(fa, v)] (get equiv fc) := by classical
  -- TODO this proof seems repetitive
  simp +unfoldPartialApp [get, setSingle'Core, CanonicalField.set,
    IteratedProd.foldMap_eq_cartesianProduct, FieldUpdateDescr.fieldUpdate, IteratedArrow.uncurry_curry,
    Function.comp]
  simp [← (FieldUpdatePat.footprint_match_iff_when_valid dec h)]
  congr! 1 ; ext args
  -- `foldr` is more convenient for induction here
  rw [List.foldl_eq_foldr_reverse]
  conv => enter [2, 1] ; rw [← List.mem_reverse]
  generalize footprint.cartesianProduct.reverse = prods
  generalize (v.uncurry) = vv
  induction prods with
  | nil => simp
  | cons p prods ih => simp [ite_or, ← ih, instl.insert_get] ; grind

instance instTotalMapLikeLawfulFieldRep : LawfulFieldRepresentation FieldDomain FieldCodomain γ
    -- TODO this is awkward; synthesis fails here
    (instTotalMapLikeAsFieldRep equiv instfin) where
  toLawfulFieldRepresentationSet :=
    LawfulFieldRepresentationSet.mkFromSingleSet ..
  get_set_idempotent := by
    introv
    apply FieldRepresentation.TotalMapLike.get_set_for_validFootprint
    apply FieldUpdatePat.footprintRaw_valid

end TotalMapLikeUpdates

namespace NotNecessarilyTotalMapLikeUpdates

-- TODO the following seems repetitive; how can we eliminate repetition?
variable {FieldDomain : List Type} {FieldCodomain : Type}
  [instd : DecidableEq α]
  [inst : TotalMapLike α FieldCodomain γ]
  [instl : LawfulTotalMapLike γ]
  (equiv : IteratedProd FieldDomain ≃ α)
  (instfin : IteratedProd (FieldDomain.map (OptionalTC ∘ Enumeration)))
  (instdeceq : IteratedProd (FieldDomain.map DecidableEq))

abbrev HybridTotalMapLike (γ) (FieldDomain : List Type) (FieldCodomain : Type) :=
  HybridFieldType γ FieldDomain FieldCodomain

def HybridTotalMapLike.get : HybridTotalMapLike γ FieldDomain FieldCodomain → CanonicalField FieldDomain FieldCodomain
  | .canonical cf => cf.inner
  | .concrete fc => delta% FieldRepresentation.TotalMapLike.get equiv fc

def HybridTotalMapLike.setSingle
  (fa : FieldUpdatePat FieldDomain)
  (v : CanonicalField FieldDomain FieldCodomain) (fc : HybridTotalMapLike γ FieldDomain FieldCodomain)
  : HybridTotalMapLike γ FieldDomain FieldCodomain :=
  match fc with
  | .canonical cf => .canonical <| CanonicalFieldWrapper.mk <| CanonicalField.set instdeceq [(fa, v)] cf.inner
  | .concrete fc' =>
    match fa.footprintRestricted instfin with
    | none => .canonical <| CanonicalFieldWrapper.mk <| CanonicalField.set instdeceq [(fa, v)]
      <| FieldRepresentation.TotalMapLike.get equiv fc'
    | some footprint => .concrete <|
      FieldRepresentation.TotalMapLike.setSingle'Core equiv v fc' footprint

instance instHybridTotalMapLikeAsFieldRep : FieldRepresentation FieldDomain FieldCodomain
  (HybridTotalMapLike γ FieldDomain FieldCodomain) :=
  FieldRepresentation.mkFromSingleSet
    (get := HybridTotalMapLike.get equiv)
    (setSingle := HybridTotalMapLike.setSingle equiv instfin instdeceq)

instance instHybridTotalMapLikeLawfulFieldRep : LawfulFieldRepresentation FieldDomain FieldCodomain
    (HybridTotalMapLike γ FieldDomain FieldCodomain)
    -- TODO this is awkward; synthesis fails here
    (instHybridTotalMapLikeAsFieldRep equiv instfin instdeceq) where
  toLawfulFieldRepresentationSet :=
    LawfulFieldRepresentationSet.mkFromSingleSet ..
  get_set_idempotent := by open Classical in
    introv ; rcases fav with ⟨fa, v⟩
    simp +unfoldPartialApp [instHybridTotalMapLikeAsFieldRep, FieldRepresentation.mkFromSingleSet,
      FieldRepresentation.set, HybridTotalMapLike.setSingle,
      HybridTotalMapLike.get]
    rcases fc with cf | fc <;> dsimp only
    · congr ; apply IteratedProd.map_DecidableEq_eq
    · rcases h : FieldUpdatePat.footprintRestricted instfin fa with _ | footprint <;> dsimp only
      · congr ; apply IteratedProd.map_DecidableEq_eq
      · apply FieldRepresentation.TotalMapLike.get_set_for_validFootprint
        apply FieldUpdatePat.footprintRestricted_valid
        apply h

end NotNecessarilyTotalMapLikeUpdates

end ConcreteUpdates

section ConcreteInstances

abbrev BitVecAsFinset (α) [FinEnum α] := BitVec (FinEnum.card α)

instance [FinEnum α] : Membership α (BitVecAsFinset α) where
  mem a b := a[FinEnum.equiv b]

instance [FinEnum α] : DecidableRel (Membership.mem (γ := BitVecAsFinset α)) := by
  dsimp only [Membership.mem] ; infer_instance

-- CHECK this might not be efficient enough; is there actually an operation
-- for setting a bit?
-- CHECK this might not be efficient, from another point, since
-- `insert` and `erase` requires yet another check of existence,
-- which is not necessary in this case
instance [FinEnum α] : FinsetLike (BitVecAsFinset α) where
  insert a b _ := b ||| (BitVec.twoPow _ (FinEnum.equiv a))
  erase a b _ := b ^^^ (BitVec.twoPow _ (FinEnum.equiv a))

instance [BEq α] [Hashable α] : FinsetLike (Std.HashSet α) where
  insert a b _ := b.insert a
  erase a b _ := b.erase a

instance {cmp : α → α → Ordering} : FinsetLike (Std.TreeSet α cmp) where
  insert a b _ := b.insert a
  erase a b _ := b.erase a

instance [FinEnum α] : LawfulFinsetLike (BitVecAsFinset α) where
  toFinset b := List.finRange (FinEnum.card α) |>.filterMap (fun a => if b[a] then some (FinEnum.equiv.symm a) else none) |>.toFinset
  toFinset_mem_iff a b := by simp ; simp [Membership.mem] ; grind
  insert_toFinset a b h := by
    ext a ; simp [FinsetLike.insert] ; grind
  erase_toFinset a b h := by
    ext a ; simp [FinsetLike.erase] ; simp [Membership.mem] at h ; grind

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

abbrev BitVecsAsFinmap (α β) [FinEnum α] [FinEnum β] :=
  BitVec ((FinEnum.card α) * (Nat.bitLength (FinEnum.card β)))

instance [FinEnum α] [FinEnum β] [Inhabited β] : TotalMapLike α β (BitVecsAsFinmap α β) where
  get mp a :=
    -- this special check is kind of annoying, but there seems no better way?
    if h : FinEnum.card β = 0 then
      let fin0 := h ▸ FinEnum.equiv (default : β)
      Fin.elim0 fin0
    else
      let ida := FinEnum.equiv a
      -- bit range: `[ida * (bitLength β), (ida + 1) * (bitLength β))`
      let bl := Nat.bitLength (FinEnum.card β)
      let res := mp.extractLsb' (ida * bl) bl
      FinEnum.equiv.symm <| Fin.minCast (FinEnum.card β) h res.toFin
  insert a b mp :=
    let ida := FinEnum.equiv a
    let bl := Nat.bitLength (FinEnum.card β)
    let offset := ida * bl
    let oldval := mp.extractLsb' offset bl
    let idb := FinEnum.equiv b
    let newval := BitVec.ofFin <| idb.castLE Nat.bitLength_range
    mp ^^^ ((newval ^^^ oldval |>.zeroExtend _) <<< offset)

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

instance [FinEnum α] [FinEnum β] [Inhabited β] : LawfulTotalMapLike (BitVecsAsFinmap α β) where
  insert_get a a' b mp := by
    dsimp only [TotalMapLike.get, TotalMapLike.insert]
    split <;> rename_i h1
    on_goal 1=> apply Fin.elim0 (h1 ▸ FinEnum.equiv (default : β))
    split_ifs with h2
    · subst a'
      have tmp1 : ↑(FinEnum.equiv a) + 1 ≤ FinEnum.card α := by grind
      rw [BitVec.extractLsb'_xor, BitVec.zeroExtend]
      rewrite (occs := .neg [1]) [← BitVec.setWidth_ushiftRight_eq_extractLsb]
      rw [BitVec.shiftLeft_then_ushiftRight_eq]
      on_goal 2=>
        rw [Nat.add_comm, Nat.mul_comm, ← Nat.mul_add_one, Nat.mul_comm]
        apply Nat.mul_le_mul_right ; assumption
      repeat rw [BitVec.setWidth_xor]
      repeat rw [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
      all_goals try apply Nat.le_mul_of_pos_left ; grind
      rewrite (occs := .pos [1]) [BitVec.xor_comm, BitVec.xor_assoc, BitVec.xor_self]
      simp only [BitVec.xor_zero, BitVec.toFin_ofFin]
      symm ; rw [← Equiv.apply_eq_iff_eq_symm_apply]
      ext ; dsimp ; symm ; trans ; apply Nat.min_eq_left
      all_goals grind
    · congr! 3
      rw [BitVec.extractLsb'_xor, BitVec.zeroExtend, BitVec.xor_getself_iff]
      ext i hi ; simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_shiftLeft]
      set ida' := ↑(FinEnum.equiv a')
      set ida := ↑(FinEnum.equiv a)
      cases h : (decide (ida' * Nat.bitLength (FinEnum.card β) + i < ida * Nat.bitLength (FinEnum.card β)))
      · simp at h
        simp only [BitVec.getLsbD_setWidth]
        rw [BitVec.getLsbD_of_ge] ; simp
        generalize Nat.bitLength (FinEnum.card β) = bl at *
        have tmp1 : (ida : Nat) < ↑ida' := by
          rcases Nat.lt_trichotomy ida ida' with hlt | heq | hgt
          · assumption
          · simp [ida', ida, ← Fin.ext_iff] at heq ; contradiction
          · have tmp2 : (↑ida' + 1) * bl ≤ ↑ida' * bl + i := by
              trans (↑ida * bl)
              · apply Nat.mul_le_mul_right ; assumption
              · assumption
            grind
        rw [Nat.sub_add_comm, ← Nat.mul_sub_right_distrib]
        on_goal 2=> exact Nat.mul_le_mul_right _ (Nat.le_of_lt tmp1)
        apply Nat.le_add_right_of_le
        apply Nat.le_mul_of_pos_left ; grind
      · simp

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
