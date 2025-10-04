import Std
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ProxyType
import Mathlib.Tactic.CongrExclamation

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

section Iterated

abbrev IteratedProd (ts : List Type) : Type :=
  ts.foldr Prod Unit

abbrev IteratedArrow (base : Type) (ts : List Type) : Type :=
  ts.foldr (· → ·) base

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
  (k : (IteratedProd ts) → base) (args : IteratedProd ts) :
  IteratedArrow.uncurry (IteratedArrow.curry k) args = k args := by
  induction ts with
  | nil => simp [IteratedProd] at k args ; simp [IteratedArrow.curry, IteratedArrow.uncurry]
  | cons t ts ih =>
    simp [IteratedProd] at k args
    rcases args with ⟨a, args⟩
    simp [IteratedArrow.curry, IteratedArrow.uncurry, ih]

def IteratedProd.patCmp {ts : List Type} (dec : ∀ ty ∈ ts, DecidableEq ty)
  (po : IteratedProd (ts.map Option)) (p : IteratedProd ts) : Bool :=
  match ts, po, p with
  | [], (), () => true
  | t :: _, (o, po'), (x, p') =>
    (o.elim true (fun y => @decide (y = x) (dec t (by simp) _ _)))
    && IteratedProd.patCmp (fun ty h => dec ty (by simp ; exact (Or.inr h))) po' p'

end Iterated

section SingleField

variable (fieldComponents : List Type) (FieldBase : Type)

local macro "⌞" t1:ident t2:ident* "⌟" : term => `($t1 $(Lean.mkIdent `fieldComponents) $t2:ident*)
local macro "⌞_" t1:ident t2:ident* "⌟" : term => `(⌞ $t1 $(Lean.mkIdent `FieldBase) $t2:ident* ⌟)

abbrev FieldUpdatePat : Type := IteratedProd <| List.map Option <| fieldComponents

abbrev CanonicalField : Type := IteratedArrow FieldBase fieldComponents

abbrev FieldUpdateDescr := List (⌞ FieldUpdatePat ⌟ × ⌞_ CanonicalField ⌟)

def fieldUpdate
  {fieldComponents : List Type}
  {FieldBase : Type}
  (dec : ∀ ty ∈ fieldComponents, DecidableEq ty)
  (favs : ⌞_ FieldUpdateDescr ⌟)
  (vbase : ⌞_ CanonicalField ⌟)
  (args : IteratedProd fieldComponents) : FieldBase :=
  favs.foldr (fun (fa, v) acc =>
    if fa.patCmp dec args then v.uncurry args else acc) (vbase.uncurry args)

class FieldRepresentation (FieldTypeConcrete : Type) where
  get : FieldTypeConcrete → ⌞_ CanonicalField ⌟
  set : ⌞_ FieldUpdateDescr ⌟ → FieldTypeConcrete → FieldTypeConcrete

class LawfulFieldRepresentation (FieldTypeConcrete : Type)
  (inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟) where
  get_set_idempotent :
    ∀ -- TODO not sure this should be made here in the argument, but using
      -- the fact that all `DecidableEq` instances are equal, this will not
      -- matter much?
      (dec : ∀ ty ∈ fieldComponents, DecidableEq ty)
      (fc : FieldTypeConcrete)
      (favs : ⌞_ FieldUpdateDescr ⌟),
      inst.get (inst.set favs fc) = IteratedArrow.curry (fieldUpdate dec favs (inst.get fc))
  set_append :
    ∀ (fc : FieldTypeConcrete)
      (favs₁ favs₂ : ⌞_ FieldUpdateDescr ⌟),
      inst.set favs₂ (inst.set favs₁ fc) = inst.set (favs₂ ++ favs₁) fc
  set_nil :
    ∀ {fc : FieldTypeConcrete}, inst.set [] fc = fc
  set_get_idempotent :
    ∀ (fc : FieldTypeConcrete) (fa : FieldUpdatePat fieldComponents),
      inst.set [(fa, inst.get fc)] fc = fc

instance canonicalFieldRepresentation {fieldComponents : List Type} {FieldBase : Type}
  (dec : ∀ ty ∈ fieldComponents, DecidableEq ty) :
  (⌞_ FieldRepresentation ⌟) (⌞_ CanonicalField ⌟) where
  get fc := fc
  set favs fc := IteratedArrow.curry (fieldUpdate dec favs fc)

instance canonicalFieldRepresentationLawful
  (dec : ∀ ty ∈ fieldComponents, DecidableEq ty) :
  LawfulFieldRepresentation fieldComponents FieldBase (⌞_ CanonicalField ⌟)
    -- TODO why synthesis fails here? is it because there is no `semiOutParam`, `outParam` or because of `dec`?
    -- also, due to the synthesis failure, `inst` cannot be declared using `[]`
    (inst := canonicalFieldRepresentation dec) where
  get_set_idempotent := by
    introv ; simp [FieldRepresentation.get, FieldRepresentation.set]
    congr ; funext ; grind only   -- ?
  set_get_idempotent := by
    introv ; simp +unfoldPartialApp [fieldUpdate, FieldRepresentation.set, FieldRepresentation.get, IteratedArrow.curry_uncurry]
  set_append := by
    introv ; simp +unfoldPartialApp [fieldUpdate, FieldRepresentation.set, IteratedArrow.uncurry_curry]
  set_nil := by
    introv ; simp +unfoldPartialApp [FieldRepresentation.set, fieldUpdate, IteratedArrow.curry_uncurry]

class FieldRepresentationEquivCanonical
  (FieldTypeConcrete : Type)
  (inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟)
  (getBack : ⌞_ CanonicalField ⌟ → FieldTypeConcrete) where
  getBack_get_id : ∀ fc, getBack (inst.get fc) = fc
  get_getBack_id : ∀ cf, inst.get (getBack cf) = cf
  set : ∀ (dec : ∀ ty ∈ fieldComponents, DecidableEq ty) favs cf,
    inst.get (inst.set favs (getBack cf)) = IteratedArrow.curry (fieldUpdate dec favs cf)

theorem FieldRepresentationEquivCanonical.set' {fieldComponents : List Type} {FieldBase : Type}
  {FieldTypeConcrete : Type}
  [inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟]
  {getBack : ⌞_ CanonicalField ⌟ → FieldTypeConcrete}
  (h : ⌞_ FieldRepresentationEquivCanonical FieldTypeConcrete inst getBack ⌟)
  (dec : ∀ ty ∈ fieldComponents, DecidableEq ty) (favs fc) :
  getBack (IteratedArrow.curry (fieldUpdate dec favs (inst.get fc))) = inst.set favs fc := by
  have h1 := h.set dec favs (inst.get fc)
  rw [h.getBack_get_id] at h1 ; rw [← h1, h.getBack_get_id]

instance FieldRepresentationEquivCanonical.toLawful
  (FieldTypeConcrete : Type)
  (inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟)
  (getBack : ⌞_ CanonicalField ⌟ → FieldTypeConcrete)
  (dec : ∀ ty ∈ fieldComponents, DecidableEq ty)
  (inst2 : ⌞_ FieldRepresentationEquivCanonical FieldTypeConcrete inst getBack ⌟)
  : LawfulFieldRepresentation fieldComponents FieldBase FieldTypeConcrete
    (inst := inst) where
  set_nil := by
    introv ; rw [← inst2.set' dec]
    simp +unfoldPartialApp [fieldUpdate, IteratedArrow.curry_uncurry, inst2.getBack_get_id]
  set_append := by
    introv
    rewrite (occs := .pos [3]) [← inst2.set' dec]
    have tmp := (⌞_ canonicalFieldRepresentationLawful dec ⌟).set_append (fc := inst.get fc) favs₁ favs₂
    dsimp only [FieldRepresentation.set] at tmp
    rw [← tmp]
    rewrite (occs := .pos [2]) [← inst2.get_getBack_id (IteratedArrow.curry _)]
    rw [inst2.set' dec] ; rw [inst2.set' dec]
  get_set_idempotent := by
    introv ; rewrite (occs := .pos [1]) [← inst2.getBack_get_id fc, inst2.set dec] ; rfl
  set_get_idempotent := by
    introv
    rewrite (occs := .pos [2, 3]) [← inst2.getBack_get_id fc]
    rewrite (occs := .pos [1]) [← inst2.getBack_get_id (FieldRepresentation.set _ _)]
    rw [inst2.set dec]
    have tmp := (⌞_ canonicalFieldRepresentationLawful dec ⌟).set_get_idempotent (fc := inst.get fc) fa
    rewrite (occs := .pos [3]) [← tmp] ; rfl

end SingleField

#exit

section FieldDefinitions

variable {FieldLabel : Type} (fieldComponents : FieldLabel → List Type)
  (FieldBase : FieldLabel → Type) (f : FieldLabel)

local macro "⌞" t1:ident t2:ident* "⌟" : term => `($t1 $(Lean.mkIdent `fieldComponents) $t2:ident*)
local macro "⌞_" t1:ident t2:ident* "⌟" : term => `($t1 $(Lean.mkIdent `fieldComponents) $(Lean.mkIdent `FieldBase) $t2:ident*)

abbrev FieldUpdatePat : Type := IteratedProd <| List.map Option <| fieldComponents f

abbrev CanonicalField : Type := IteratedArrow (FieldBase f) (fieldComponents f)

abbrev CanonicalFields : Type := ∀ f, ⌞_ CanonicalField f ⌟

abbrev FieldUpdateDescr :=
  List (⌞ FieldUpdatePat f ⌟ × ⌞_ CanonicalField f ⌟)

def fieldUpdate
  {fieldComponents : FieldLabel → List Type}
  {FieldBase : FieldLabel → Type}
  {f : FieldLabel}
  (dec : ∀ ty ∈ fieldComponents f, DecidableEq ty)
  (favs : ⌞_ FieldUpdateDescr f ⌟)
  (vbase : ⌞_ CanonicalField f ⌟)
  (args : IteratedProd (fieldComponents f)) : FieldBase f :=
  favs.foldr (fun (fa, v) acc =>
    if fa.patCmp dec args then v.uncurry args else acc) (vbase.uncurry args)

/-
-- TODO this might have the not-necessarily-separate issue
class StateRepresentation (St : Type u) (FieldType : FieldLabel → Type) where
  getField : (f : FieldLabel) → St → FieldType f
  setField : {f : FieldLabel} → St → FieldType f → St
-/

class FieldRepresentation (FieldTypeConcrete : FieldLabel → Type) where
  get : {f : FieldLabel} → FieldTypeConcrete f → ⌞_ CanonicalField f ⌟
  set : {f : FieldLabel} → ⌞_ FieldUpdateDescr f ⌟ → FieldTypeConcrete f → FieldTypeConcrete f

class LawfulStateRepresentation (St : Type u) (FieldType : FieldLabel → Type)
  [inst : StateRepresentation St FieldType] where
  getField_setField_idempotent :
    ∀ {f : FieldLabel} (st : St) (fc : FieldType f),
      inst.getField _ (inst.setField st fc) = fc
  setField_setField_last :
    ∀ {f : FieldLabel} (st : St) (fc₁ fc₂ : FieldType f),
      inst.setField (inst.setField st fc₁) fc₂ = inst.setField st fc₂
  setField_getField_idempotent :
    ∀ (f : FieldLabel) (st : St),
      inst.setField st (inst.getField f st) = st

class LawfulFieldRepresentation (FieldTypeConcrete : FieldLabel → Type)
  (inst : FieldRepresentation fieldComponents FieldBase FieldTypeConcrete) where
  get_set_idempotent :
    ∀ {f : FieldLabel}
      -- TODO not sure this should be made here in the argument, but using
      -- the fact that all `DecidableEq` instances are equal, this will not
      -- matter much?
      (dec : ∀ ty ∈ fieldComponents f, DecidableEq ty)
      (fc : FieldTypeConcrete f)
      (favs : ⌞_ FieldUpdateDescr f ⌟),
      inst.get (inst.set favs fc) = IteratedArrow.curry (fieldUpdate dec favs (inst.get fc))
  set_append :
    ∀ (f : FieldLabel) (fc : FieldTypeConcrete f)
      (favs₁ favs₂ : ⌞_ FieldUpdateDescr f ⌟),
      inst.set favs₂ (inst.set favs₁ fc) = inst.set (favs₂ ++ favs₁) fc
  set_nil :
    ∀ {f : FieldLabel} {fc : FieldTypeConcrete f}, inst.set [] fc = fc
  set_get_idempotent :
    ∀ (f : FieldLabel) (fc : FieldTypeConcrete f) (fa : FieldUpdatePat fieldComponents f),
      inst.set [(fa, inst.get fc)] fc = fc

-- side question: is it possible to prove something about `StateRepresentation`,
-- by proving something about the canonical representation?
-- this seems to be related to the idea of parametricity?

variable [DecidableEq FieldLabel] in
instance canonicalStateRepresentation : StateRepresentation (⌞_ CanonicalFields ⌟) (⌞_ CanonicalField ⌟) where
  getField f st := st f
  setField {f} st fc := fun l => if h : f = l then h ▸ fc else st l

variable [DecidableEq FieldLabel] in
instance : LawfulStateRepresentation (⌞_ CanonicalFields ⌟) (⌞_ CanonicalField ⌟) where
  getField_setField_idempotent := by
    introv ; simp [StateRepresentation.getField, StateRepresentation.setField]
  setField_setField_last := by
    introv ; simp [StateRepresentation.setField]
    funext f ; split <;> ((try subst_eqs) ; (try simp))
  setField_getField_idempotent := by
    introv ; simp [StateRepresentation.setField, StateRepresentation.getField]
    funext f ; split <;> ((try subst_eqs) ; (try simp))

instance canonicalFieldRepresentation (dec : ∀ f, ∀ ty ∈ fieldComponents f, DecidableEq ty) :
  FieldRepresentation fieldComponents FieldBase (⌞_ CanonicalField ⌟) where
  get fc := fc
  set {f} favs fc := IteratedArrow.curry (fieldUpdate (dec f) favs fc)

instance (dec : ∀ f, ∀ ty ∈ fieldComponents f, DecidableEq ty) :
  LawfulFieldRepresentation fieldComponents FieldBase (⌞_ CanonicalField ⌟)
    -- TODO why synthesis fails here? is it because there is no `semiOutParam`, `outParam` or because of `dec`?
    -- also, due to the synthesis failure, `inst` cannot be declared using `[]`
    (inst := canonicalFieldRepresentation fieldComponents FieldBase dec) where
  get_set_idempotent := by
    introv ; simp [FieldRepresentation.get, FieldRepresentation.set]
    congr ; funext ; grind only   -- ?
  set_get_idempotent := by
    introv ; simp +unfoldPartialApp [fieldUpdate, FieldRepresentation.set, FieldRepresentation.get, IteratedArrow.curry_uncurry]
  set_append := by
    introv ; simp +unfoldPartialApp [fieldUpdate, FieldRepresentation.set, IteratedArrow.uncurry_curry]
  set_nil := by
    introv ; simp +unfoldPartialApp [FieldRepresentation.set, fieldUpdate, IteratedArrow.curry_uncurry]

end FieldDefinitions

end Veil
