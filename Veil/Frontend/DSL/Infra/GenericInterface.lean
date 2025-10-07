import Std
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ProxyType
import Mathlib.Tactic.CongrExclamation
import Mathlib.Data.FinEnum

/-! # Generic Interface for State Representation

## Key Questions

1. How to represent the interface? What are needed?
2. How to relate the canonical representation with the _equivalent_
   one? What can we get? Can we avoid some metaprogramming here?
3. How to actually use the laws during verification?

## Elements of the Interface

"Getting the value from a field" and "getting the field from a
structure" should be seperate.

Usually, the modification to the field or the structure is done by
- getting a new field according to a description, and
- setting it back to the structure using `modifyGet`

So axiomatize each of these operations.

The laws should be similar to the ones about `SubState` (an empirical
observation).

TODO How are these related to lenses?

## Design Choices

Use dependent types. This might be actually a relatively _cheap_
(in the sense that the use of dependent types are not very horrible
here) way to make things work and make the metatheory reusable
(less metaprogramming).

When stating the law about `get (set ... fc)` where `fc` is the concrete
representation of the field, the idea is to push `get` inside and obtain
something like `op ... (get fc)`.

By observing the original "tuple update", the _field update pattern_
should be a tuple of `Option`al values, where `none` indicates a
∀-quantified variable.

The easiest way to describe the term on the RHS of `:=` is to make it
into a function. It turns out this function can have the type
`CanonicalField` below.

The reference implementation of a field (`CanonicalField`) appears in
multiple places. When transforming a concrete representation of a field
to it, it is like "exposing" the field. It is also used to represent
the term on the RHS of `:=`, and hence it appears in the `set` operation.
Another important role is that we need to use its form in the
verification condition (see below).

To state the law about `set (set ... fc)`, the general idea is to
reduce it into a single `set`. However, if `set` is defined on only
a single update pattern and a single `CanonicalField`, then there is
no good way to merge two patterns and two `CanonicalField`s together.
So instead of merging them, we simply _pile them up_; specifically,
we make `set` take a _list_ of patterns and `CanonicalField`s.
The `set` shall be "eliminated" by a surrounding `get` when needed,
by using the law about `get (set ... fc)`.
- An alternative approach that does not use piling up is to allow
  multiple update patterns to correspond to the same field update.
  In that case, merging two updates into one is more or less
  straightforward. But that might introduce redundant checks in `if`.


TODO

-/

namespace Veil

-- NOTE: Currently, the following does not consider universe polymorphism.
-- TODO any way to specialize all these dependently-typed definitions to make them faster?
-- maybe some are not necessary since these are only used for proofs?

section Iterated

-- TODO I believe this kind of things must have been formalized & proved
-- before. find them!

abbrev IteratedProd (ts : List Type) : Type :=
  ts.foldr Prod Unit

abbrev IteratedProd' (ts : List Type) : Type :=
  match ts with
  | [] => Unit
  | t :: ts' => t × IteratedProd ts'

abbrev IteratedArrow (base : Type) (ts : List Type) : Type :=
  ts.foldr (· → ·) base

def IteratedProd.append {ts1 ts2 : List Type}
  (p1 : IteratedProd ts1) (p2 : IteratedProd ts2) : IteratedProd (ts1 ++ ts2) :=
  match ts1, p1 with
  | [], _ => p2
  | _ :: _, (a, p1) => (a, IteratedProd.append p1 p2)

instance : HAppend (IteratedProd ts1) (IteratedProd ts2)
  (IteratedProd (ts1 ++ ts2)) where
  hAppend := IteratedProd.append

def IteratedProd.default {ts : List Type}
  {T : Type → Type}
  (default : ∀ (ty : Type), T ty)
  : IteratedProd (ts.map T) :=
  match ts with
  | [] => ()
  | t :: _ => (default t, IteratedProd.default default)

def IteratedArrow.curry {base : Type} {ts : List Type}
  (k : (IteratedProd ts) → base) : IteratedArrow base ts :=
  match ts with
  | [] => k ()
  | t :: _ =>
    fun (x : t) => IteratedArrow.curry (fun xs => k (x, xs))

def IteratedArrow.uncurry {base : Type} {ts : List Type}
  (f : IteratedArrow base ts) (args : IteratedProd ts) : base :=
  match ts, f, args with
  | [], f, () => f
  | _ :: _, f, (x, xs) => IteratedArrow.uncurry (f x) xs

theorem IteratedArrow.curry_uncurry {base : Type} {ts : List Type}
  (a : IteratedArrow base ts) :
  IteratedArrow.curry (fun args => a.uncurry args) = a := by
  induction ts with
  | nil => simp [IteratedArrow.curry, IteratedArrow.uncurry]
  | cons t ts ih =>
    simp [IteratedArrow.curry, IteratedArrow.uncurry]
    funext x ; specialize ih (a x) ; rw [ih]

theorem IteratedArrow.uncurry_curry {base : Type} {ts : List Type}
  (k : (IteratedProd ts) → base) :
  IteratedArrow.uncurry (IteratedArrow.curry k) = k := by
  funext args
  induction ts with
  | nil => simp [IteratedProd] at k args ; simp [IteratedArrow.curry, IteratedArrow.uncurry]
  | cons t ts ih =>
    simp [IteratedProd] at k args
    rcases args with ⟨a, args⟩
    simp [IteratedArrow.curry, IteratedArrow.uncurry, ih]

-- CHECK not sure if this is actually "fold"
def IteratedProd.fold {ts : List Type} {T₁ T₂ : Type → Type}
  (base : T₂ Unit)
  (prod : ∀ {tya tyb : Type}, T₁ tya → T₂ tyb → T₂ (tya × tyb))
  (elements : IteratedProd (ts.map T₁)) : T₂ (IteratedProd ts) :=
  match ts, elements with
  | [], _ => base
  | _ :: _, (lis, elements) => prod lis <| IteratedProd.fold base prod elements

def IteratedProd.map {ts : List Type} {T₁ T₂ : Type → Type}
  (map : ∀ {ty : Type}, T₁ ty → T₂ ty)
  (elements : IteratedProd (ts.map T₁)) : IteratedProd (ts.map T₂) :=
  match ts, elements with
  | [], _ => ()
  | _ :: _, (lis, elements) => (map lis, IteratedProd.map map elements)

def IteratedProd.zipWith {ts : List Type} {T₁ T₂ T₃ : Type → Type}
  (elements₁ : IteratedProd (ts.map T₁))
  (elements₂ : IteratedProd (ts.map T₂))
  (zip : ∀ {ty : Type}, T₁ ty → T₂ ty → T₃ ty) : IteratedProd (ts.map T₃) :=
  match ts, elements₁, elements₂ with
  | [], _, _ => ()
  | _ :: _, (e₁, elements₁), (e₂, elements₂) =>
    (zip e₁ e₂, IteratedProd.zipWith elements₁ elements₂ zip)

-- TODO does this really implement lazy & cacheable evaluation?
-- or is there any other more authentic way to do this in Lean?
def IteratedProd.cartesianProduct {ts : List Type}
  (elements : IteratedProd (ts.map (Unit → List ·))) :=
  IteratedProd.fold [()] (List.product <| · ()) elements

section ListTypeAll

abbrev List.typesAll (T : Type → Type) (ts : List Type) := ∀ ty ∈ ts, T ty

def List.typesAll.toIteratedProd {T : Type → Type} {ts : List Type}
  (lta : List.typesAll T ts) : IteratedProd (ts.map T) :=
  match ts with
  | [] => ()
  | t :: ts' =>
    let lta' : List.typesAll T ts' := fun ty h => lta ty (by simp ; exact Or.inr h)
    (lta t (by simp), lta'.toIteratedProd)

instance instDecidableEqIteratedProd (inst : List.typesAll DecidableEq ts) :
  DecidableEq (IteratedProd ts) :=
    inst.toIteratedProd.fold (inferInstanceAs (DecidableEq Unit)) (@instDecidableEqProd)

-- TODO the code for `IteratedProd'` is a repetitive
instance instDecidableEqIteratedProd' (inst : List.typesAll DecidableEq ts) : DecidableEq (IteratedProd' ts) :=
  match ts with
  | [] => inferInstanceAs (DecidableEq Unit)
  | _ :: _ => instDecidableEqIteratedProd inst

instance instHashableIteratedProd (inst : List.typesAll Hashable ts) :
  Hashable (IteratedProd ts) :=
    inst.toIteratedProd.fold (inferInstanceAs (Hashable Unit)) (@instHashableProd)

instance instHashableIteratedProd' (inst : List.typesAll Hashable ts) : Hashable (IteratedProd' ts) :=
  match ts with
  | [] => inferInstanceAs (Hashable Unit)
  | _ :: _ => instHashableIteratedProd inst

end ListTypeAll

section IteratedProdInstances

macro "infer_instance_for_iterated_prod" : tactic =>
  `(tactic| repeat' (first | constructor | infer_instance ))

end IteratedProdInstances

-- TODO any existing way to define this kind of shortcutting comparison function?
-- maybe something like `fold₂`? or use thunks?
def IteratedProd.patCmp {ts : List Type} {T : Type → Type}
  (cmp : ∀ {ty : Type} [DecidableEq ty], T ty → ty → Bool)
  (dec : IteratedProd (ts.map DecidableEq))
  (po : IteratedProd (ts.map T)) (p : IteratedProd ts) : Bool :=
  match ts, po, p with
  | [], (), () => true
  | _ :: _, (o, po'), (x, p') =>
    (@cmp _ dec.1 o x) && IteratedProd.patCmp cmp dec.2 po' p'

theorem IteratedProd.map_DecidableEq_eq {ts : List Type}
  (dec dec' : IteratedProd (ts.map DecidableEq)) : dec = dec' := by
  induction ts with
  | nil => simp [IteratedProd] at dec dec' ⊢
  | cons t ts ih =>
    simp [IteratedProd] at dec dec' ⊢
    rcases dec with ⟨d, dec⟩ ; rcases dec' with ⟨d', dec'⟩
    simp ; constructor ; clear dec dec' ih ts ; grind /- ?? -/ ; apply ih

section HashMapAndSet

-- NOTE: Since we are doing some very nice-looking equality reasoning here,
-- we use `Std.ExtHashSet` instead of `Std.HashSet` to use the extensionality.
-- Maybe this is not necessary; we will see.

abbrev HashSetForIteratedProd (ts : List Type)
  [instd : DecidableEq (IteratedProd ts)]
  [insth : Hashable (IteratedProd ts)] := Std.ExtHashSet (IteratedProd ts)

variable {ts : List Type} [instd : DecidableEq (IteratedProd ts)]
  [insth : Hashable (IteratedProd ts)]
  (instfin : IteratedProd (ts.map FinEnum))

instance instHashSetForIteratedProdEquivIteratedArrowToBool :
  HashSetForIteratedProd ts ≃ IteratedArrow Bool ts where
  toFun hs := IteratedArrow.curry hs.contains
  -- we should not have to care about the performance of this function ...?
  invFun f := Std.ExtHashSet.ofList
    (instfin.fold (inferInstanceAs (FinEnum Unit)) (@FinEnum.prod) |>.toList _
      |>.filter f.uncurry)
  left_inv := by
    simp [Function.LeftInverse] ; intro hs ; simp [IteratedArrow.uncurry_curry]
    ext k ; simp
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse] ; intro f
    rewrite (occs := .neg [1]) [← IteratedArrow.curry_uncurry f]
    congr ; ext k ; simp

-- this is problematic; the equivalence holds only when the domain
-- of the `ExtHashMap` is full
/-
abbrev HashMapForIteratedProd (ts : List Type)
  [instd : DecidableEq (IteratedProd ts)]
  [insth : Hashable (IteratedProd ts)] (base : Type) := Std.HashMap (IteratedProd ts) base

instance instHashMapForIteratedProdEquivIteratedArrow :
  HashMapForIteratedProd ts base ≃ IteratedArrow base ts where
-/

end HashMapAndSet

end Iterated

section SingleField

variable (fieldComponents : List Type) (FieldBase : Type)

local macro "⌞" t1:ident t2:ident* "⌟" : term => `($t1 $(Lean.mkIdent `fieldComponents) $t2:ident*)
local macro "⌞_" t1:ident t2:ident* "⌟" : term => `(⌞ $t1 $(Lean.mkIdent `FieldBase) $t2:ident* ⌟)

abbrev FieldUpdatePat : Type := IteratedProd (fieldComponents.map Option)

abbrev CanonicalField : Type := IteratedArrow FieldBase fieldComponents

abbrev FieldUpdateDescr := List (⌞ FieldUpdatePat ⌟ × ⌞_ CanonicalField ⌟)

def FieldUpdatePat.pad (n : Nat) : IteratedArrow (FieldUpdatePat fieldComponents)
    (fieldComponents.take n |>.map Option) :=
  IteratedArrow.curry fun args => (by
    let res := args ++ IteratedProd.default (ts := fieldComponents.drop n) (@Option.none)
    simp at res
    exact res)

def FieldUpdatePat.match
  {fieldComponents : List Type}
  (dec : IteratedProd (fieldComponents.map DecidableEq))
  (fa : FieldUpdatePat fieldComponents) args :=
  IteratedProd.patCmp (fun o x => o.elim true (fun y => decide (y = x))) dec fa args

def FieldUpdateDescr.fieldUpdate
  {fieldComponents : List Type}
  {FieldBase : Type}
  (dec : IteratedProd (fieldComponents.map DecidableEq))
  (favs : ⌞_ FieldUpdateDescr ⌟)
  (vbase : ⌞_ CanonicalField ⌟)
  (args : IteratedProd fieldComponents) : FieldBase :=
  favs.foldr (init := vbase.uncurry args) fun (fa, v) acc => if fa.match dec args then v.uncurry args else acc

def FieldUpdatePat.footprintRaw
  {fieldComponents : List Type}
  (instfin : IteratedProd (fieldComponents.map FinEnum))
  (fa : FieldUpdatePat fieldComponents) :=
  instfin.zipWith fa fun fin b =>
    b.elim (fun (_ : Unit) => fin.toList _) (fun x _ => [x])

theorem FieldUpdatePat.footprint_match_iff
  {fieldComponents : List Type}
  (instfin : IteratedProd (fieldComponents.map FinEnum))
  (dec : IteratedProd (fieldComponents.map DecidableEq))
  {fa : FieldUpdatePat fieldComponents} :
  ∀ args, args ∈ (fa.footprintRaw instfin).cartesianProduct ↔ fa.match dec args := by
  intro args
  induction fieldComponents
  all_goals (simp [FieldUpdatePat] at fa ; simp [IteratedProd] at instfin dec args)
  next => simp [IteratedProd.cartesianProduct, IteratedProd.fold, FieldUpdatePat.match] ; rfl
  next t ts ih =>
    rcases fa with ⟨b, fa⟩ ; rcases instfin with ⟨fin, instfin⟩
    rcases dec with ⟨d, dec⟩ ; rcases args with ⟨a, args⟩
    simp [IteratedProd.cartesianProduct, FieldUpdatePat.match, IteratedProd.patCmp]
    unfold FieldUpdatePat.match at ih ; rw [← ih instfin] ; clear ih
    simp [IteratedProd.cartesianProduct, FieldUpdatePat.footprintRaw, IteratedProd.zipWith, IteratedProd.fold]
    intro _ ; rcases b with _ | b <;> simp ; grind

class FieldRepresentation (FieldTypeConcrete : Type) where
  get : FieldTypeConcrete → ⌞_ CanonicalField ⌟
  set : ⌞_ FieldUpdateDescr ⌟ → FieldTypeConcrete → FieldTypeConcrete

-- a handy notation
abbrev FieldRepresentation.setSingle {fieldComponents : List Type}
  {FieldBase FieldTypeConcrete : Type}
  [self : ⌞_ FieldRepresentation FieldTypeConcrete ⌟]
  (fa : ⌞ FieldUpdatePat ⌟) (v : ⌞_ CanonicalField ⌟) (fc : FieldTypeConcrete) : FieldTypeConcrete :=
  self.set [(fa, v)] fc

-- TODO can this be declared as `instance`?
def FieldRepresentation.mkFromSingleSet {fieldComponents : List Type}
  {FieldBase : Type} {FieldTypeConcrete : Type}
  (get : FieldTypeConcrete → ⌞_ CanonicalField ⌟)
  (setSingle : ⌞ FieldUpdatePat ⌟ → ⌞_ CanonicalField ⌟ → FieldTypeConcrete → FieldTypeConcrete) :
  ⌞_ FieldRepresentation FieldTypeConcrete ⌟ where
  get := get
  set favs fc := favs.foldr (init := fc) fun (fa, v) acc => setSingle fa v acc

class LawfulFieldRepresentationSet (FieldTypeConcrete : Type)
  (inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟) where
  -- NOTE: If `set` is defined as `foldr` of `setSingle`, then the following
  -- two laws automatically hold.
  set_append :
    ∀ (favs₁ favs₂ : ⌞_ FieldUpdateDescr ⌟) (fc : FieldTypeConcrete),
      inst.set favs₂ (inst.set favs₁ fc) = inst.set (favs₂ ++ favs₁) fc
  set_nil :
    ∀ {fc : FieldTypeConcrete}, inst.set [] fc = fc

theorem LawfulFieldRepresentationSet.mkFromSingleSet {fieldComponents : List Type}
  {FieldBase : Type} {FieldTypeConcrete : Type}
  (get : FieldTypeConcrete → ⌞_ CanonicalField ⌟)
  (setSingle : ⌞ FieldUpdatePat ⌟ → ⌞_ CanonicalField ⌟ → FieldTypeConcrete → FieldTypeConcrete) :
  (⌞_ LawfulFieldRepresentationSet FieldTypeConcrete ⌟)
    (FieldRepresentation.mkFromSingleSet get setSingle) where
  set_append := by
    introv ; simp [FieldRepresentation.mkFromSingleSet, FieldRepresentation.set]
  set_nil := by
    introv ; simp [FieldRepresentation.mkFromSingleSet, FieldRepresentation.set]

class LawfulFieldRepresentation (FieldTypeConcrete : Type)
  (inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟)
  extends ⌞_ LawfulFieldRepresentationSet FieldTypeConcrete inst ⌟ where
  get_set_idempotent :
    ∀ -- TODO not sure this should be made here in the argument, but using
      -- the fact that all `DecidableEq` instances are equal, this will not
      -- matter much?
      (dec : IteratedProd (fieldComponents.map DecidableEq))
      (fc : FieldTypeConcrete)
      (favs : ⌞_ FieldUpdateDescr ⌟),
      inst.get (inst.set favs fc) = IteratedArrow.curry (favs.fieldUpdate dec (inst.get fc))
  set_get_idempotent :
    ∀ (fc : FieldTypeConcrete) (fa : FieldUpdatePat fieldComponents),
      inst.set [(fa, inst.get fc)] fc = fc

def CanonicalField.set {fieldComponents : List Type} {FieldBase : Type}
  (dec : IteratedProd (fieldComponents.map DecidableEq))
  (favs : ⌞_ FieldUpdateDescr ⌟)
  (fc : ⌞_ CanonicalField ⌟) : ⌞_ CanonicalField ⌟ :=
  IteratedArrow.curry (favs.fieldUpdate dec fc)

instance canonicalFieldRepresentation {fieldComponents : List Type} {FieldBase : Type}
  (dec : IteratedProd (fieldComponents.map DecidableEq)) :
  (⌞_ FieldRepresentation ⌟) (⌞_ CanonicalField ⌟) where
  get := id
  set favs fc := fc.set dec favs

instance canonicalFieldRepresentationLawful
  (dec : IteratedProd (fieldComponents.map DecidableEq)) :
  LawfulFieldRepresentation fieldComponents FieldBase (⌞_ CanonicalField ⌟)
    -- TODO why synthesis fails here? is it because there is no `semiOutParam`, `outParam` or because of `dec`?
    -- also, due to the synthesis failure, `inst` cannot be declared using `[]`
    (inst := canonicalFieldRepresentation dec) where
  get_set_idempotent := by
    introv ; simp [FieldRepresentation.get, FieldRepresentation.set]
    congr ; apply IteratedProd.map_DecidableEq_eq
  set_get_idempotent := by
    introv ; simp +unfoldPartialApp [CanonicalField.set, FieldUpdateDescr.fieldUpdate, FieldRepresentation.set, FieldRepresentation.get, IteratedArrow.curry_uncurry]
  set_append := by
    introv ; simp +unfoldPartialApp [CanonicalField.set, FieldUpdateDescr.fieldUpdate, FieldRepresentation.set, IteratedArrow.uncurry_curry]
  set_nil := by
    introv ; simp +unfoldPartialApp [CanonicalField.set, FieldRepresentation.set, FieldUpdateDescr.fieldUpdate, IteratedArrow.curry_uncurry]

class FieldRepresentationEquivCanonical
  (FieldTypeConcrete : Type)
  (inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟)
  -- CHECK making `getBack` an argument will make `getBack` has to take an argument
  -- of `inst`, which might be inconvenient; but explicitly providing `getBack`
  -- might be more inconvenient?
  (getBack : ⌞_ CanonicalField ⌟ → FieldTypeConcrete) where
  getBack_get_id : ∀ fc, getBack (inst.get fc) = fc
  get_getBack_id : ∀ cf, inst.get (getBack cf) = cf
  -- TODO should be easily transforming between equivalent statements
  set : ∀ (dec : IteratedProd (fieldComponents.map DecidableEq)) favs cf,
    inst.set favs (getBack cf) = getBack (cf.set dec favs)

/-- The `set` law of `FieldRepresentationEquivCanonical` can be derived
    from `LawfulFieldRepresentationSet` plus a premise only about a single update pattern. -/
theorem LawfulFieldRepresentationSet.set_canonical {fieldComponents : List Type} {FieldBase : Type}
  {FieldTypeConcrete : Type}
  (inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟)
  (inst2 : ⌞_ LawfulFieldRepresentationSet FieldTypeConcrete inst ⌟)
  {getBack : ⌞_ CanonicalField ⌟ → FieldTypeConcrete}
  (set_single : ∀ (dec : IteratedProd (fieldComponents.map DecidableEq)) fa v cf,
    inst.set [(fa, v)] (getBack cf) = getBack (cf.set dec [(fa, v)]))
  (dec : IteratedProd (fieldComponents.map DecidableEq)) favs cf :
    inst.set favs (getBack cf) = getBack (cf.set dec favs) := by
  induction favs with
  | nil => simp +unfoldPartialApp [inst2.set_nil, CanonicalField.set,
    FieldUpdateDescr.fieldUpdate, IteratedArrow.curry_uncurry]
  | cons fav favs ih =>
    have tmp := inst2.set_append favs [fav]
    simp at tmp ; rw [← tmp, ih, set_single dec]
    simp +unfoldPartialApp [CanonicalField.set, FieldUpdateDescr.fieldUpdate, IteratedArrow.uncurry_curry]

theorem FieldRepresentationEquivCanonical.mkFromGetEquiv {fieldComponents : List Type} {FieldBase : Type}
  {FieldTypeConcrete : Type}
  (inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟)
  (equiv : FieldTypeConcrete ≃ ⌞_ CanonicalField ⌟)
  (h : inst.get = equiv.toFun)
  -- TODO this statement is repeating
  (set : ∀ (dec : IteratedProd (fieldComponents.map DecidableEq)) favs cf,
    inst.set favs (equiv.symm cf) = equiv.symm (cf.set dec favs)) :
  ⌞_ FieldRepresentationEquivCanonical FieldTypeConcrete inst equiv.symm ⌟ where
  getBack_get_id := by introv ; rw [h] ; simp
  get_getBack_id := by introv ; rw [h] ; simp
  set := set

instance FieldRepresentationEquivCanonical.toLawful
  (FieldTypeConcrete : Type)
  {inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟}
  {getBack : ⌞_ CanonicalField ⌟ → FieldTypeConcrete}
  (dec : IteratedProd (fieldComponents.map DecidableEq))
  (inst2 : ⌞_ FieldRepresentationEquivCanonical FieldTypeConcrete inst getBack ⌟)
  : LawfulFieldRepresentation fieldComponents FieldBase FieldTypeConcrete
    (inst := inst) where
  set_nil := by
    introv ; rw [← inst2.getBack_get_id fc, inst2.set dec]
    simp +unfoldPartialApp [CanonicalField.set, FieldUpdateDescr.fieldUpdate, IteratedArrow.curry_uncurry, inst2.getBack_get_id]
  set_append := by
    introv ; rw [← inst2.getBack_get_id fc, inst2.set dec, inst2.set dec, inst2.set dec]
    have tmp := (⌞_ canonicalFieldRepresentationLawful dec ⌟).set_append (fc := inst.get fc) favs₁ favs₂
    dsimp only [FieldRepresentation.set] at tmp
    rw [← tmp]
  get_set_idempotent := by
    introv ; rewrite (occs := .pos [1]) [← inst2.getBack_get_id fc, inst2.set dec, inst2.get_getBack_id] ; rfl
  set_get_idempotent := by
    introv
    rewrite (occs := .pos [2, 3]) [← inst2.getBack_get_id fc]
    rw [inst2.set dec]
    have tmp := (⌞_ canonicalFieldRepresentationLawful dec ⌟).set_get_idempotent (fc := inst.get fc) fa
    rewrite (occs := .pos [3]) [← tmp] ; rfl

section HashSetAsField

instance (priority := high + 1)
  : FieldRepresentation [] FieldBase FieldBase where
  get := id
  set favs fc := List.head? favs |>.elim fc Prod.snd

instance (priority := high + 1)
  : FieldRepresentationEquivCanonical [] FieldBase FieldBase inferInstance id where
  getBack_get_id := by intro fc ; rfl
  get_getBack_id := by intro cf ; rfl
  set dec favs cf := by rcases favs with _ | ⟨⟨_, v⟩, _⟩ <;> rfl

omit fieldComponents

variable {fieldComponents : List Type}
  [instd : DecidableEq (IteratedProd fieldComponents)]
  [insth : Hashable (IteratedProd fieldComponents)]
  (instfin : IteratedProd (fieldComponents.map FinEnum))  -- TODO add a tactic for automatically constructing this (or, these)

-- CHECK It might be interesting to use a hybrid representation; e.g.,
-- mixing the use of hashmap and function? For a fully map representation,
-- it might take a lot of space, although the access is fast; for the
-- function representation, it might be slow to access (when the closure
-- is deep), but it allows a smaller "description" which might result in
-- fast computation of the target value and small space usage.
-- One difficulty is that deriving `LawfulFieldRepresentation` by
-- isomorphism _might_ be difficult (e.g., directly representing using
-- a pair of function and hashmap is not feasible, because there would
-- be no isomorphism); one potential way to work around is to only use
-- the function, but allow the function to be a wrapper of a hashmap.

-- CHECK another chance to make things more efficient is to exploit
-- some properties of the description. for example, if the description
-- is `false`, then we only need to examine the entries that are already
-- in the hashset.
-- this might be related to how queries are optimized in database queries.

-- NOTE: It might be overly strong to require `FinEnum` here. In general,
-- a footprint can be computed from the `fieldUpdatePattern`, and we only
-- need to impose the finiteness condition on the footprint.
-- However, if we are going to derive `LawfulFieldRepresentation` by
-- isomorphism, then we have to impose `FinEnum` here (otherwise the
-- isomorphism cannot be established).

-- CHECK will writing this in a recursive way, instead of constructing
-- all things to be (potentially) modified, be more efficient?

-- TODO there are two ways of implementation: (1) `fold` and (2) `let mut` with loop.
-- which is faster? do both use the object linearly?

def HashSetForIteratedProd.update
  (fa : FieldUpdatePat fieldComponents)
  (v : CanonicalField fieldComponents Bool)
  (hs : HashSetForIteratedProd fieldComponents) : HashSetForIteratedProd fieldComponents := Id.run do
  let elements := fa.footprintRaw instfin
  let vv := v.uncurry
  let prods := elements.cartesianProduct
  let mut res := hs
  for p in prods do
    let in? := res.contains p
    let in?' := vv p
    if in? && !in?' then
      res := res.erase p
    else if !in? && in?' then
      res := res.insert p
  return res

-- TODO this is very awkward ... due to the use of `IteratedArrow.curry`,
-- we cannot directly use `IteratedProd'` here. but will this redundant
-- `Unit` cause performance issue?
-- also, might also need to reflect on the interface of `get`; does it
-- introduce unnecessary overhead?
instance (priority := high) instHashSetForIteratedProdAsFieldRepresentation
  : FieldRepresentation fieldComponents Bool (HashSetForIteratedProd fieldComponents) :=
  FieldRepresentation.mkFromSingleSet
    (get := fun fc => IteratedArrow.curry fc.contains)
    (setSingle := HashSetForIteratedProd.update instfin)

instance (priority := high) instHashSetForIteratedProdEquivCanonical
  : FieldRepresentationEquivCanonical fieldComponents Bool
    (HashSetForIteratedProd fieldComponents)
    -- TODO this is awkward; synthesis fails here, and the `equiv.symm` is weird
    (instHashSetForIteratedProdAsFieldRepresentation instfin)
    (instHashSetForIteratedProdEquivIteratedArrowToBool instfin |>.symm) :=
  FieldRepresentationEquivCanonical.mkFromGetEquiv _ _ rfl
    (LawfulFieldRepresentationSet.set_canonical _
      (LawfulFieldRepresentationSet.mkFromSingleSet ..)
      (by
        introv
        simp [FieldRepresentation.mkFromSingleSet, FieldRepresentation.set, instHashSetForIteratedProdEquivIteratedArrowToBool, HashSetForIteratedProd.update]
        conv =>
          enter [1, 1, 3, p, r] ; simp [pure]
          repeat rw [← apply_ite ForInStep.yield]
          conv => enter [1] ; rw [← Id.run_pure (ite ..)] ; dsimp only [pure]
          rw [← Id.run_map _ ForInStep.yield]
        trans ; apply List.idRun_forIn_yield_eq_foldl
        ext args ; simp +unfoldPartialApp [CanonicalField.set, IteratedArrow.uncurry_curry, FieldUpdateDescr.fieldUpdate]
        simp [← (FieldUpdatePat.footprint_match_iff instfin dec)]
        -- `foldr` is more convenient for induction here
        rw [List.foldl_eq_foldr_reverse]
        rewrite (occs := .neg [1]) [← List.reverse_reverse (IteratedProd.cartesianProduct ..)]
        generalize (fa.footprintRaw instfin).cartesianProduct.reverse = prods
        simp only [List.mem_reverse]
        generalize e : (fun x y => _) = ff
        induction prods with
        | nil => simp
        | cons p prods ih =>
          simp [ite_or, ← ih] ; clear ih
          generalize (List.foldr ..) = acc
          subst ff ; simp [Id.run] ; split_ifs <;> grind
        ))

end HashSetAsField

-- section TreeSetOrMapAsField

-- instance (priority := high) : FieldRepresentation fieldComponents Bool
--   (Std.TreeSet (IteratedProd' fieldComponents)) where
--   get : FieldTypeConcrete → ⌞_ CanonicalField ⌟
--   set : ⌞_ FieldUpdateDescr ⌟ → FieldTypeConcrete → FieldTypeConcrete

-- #check Std.TreeSet

-- end TreeSetOrMapAsField

end SingleField

end Veil
