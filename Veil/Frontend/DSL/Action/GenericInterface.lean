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

abbrev IteratedProd (ts : List Type) : Type :=
  ts.foldr Prod Unit

abbrev IteratedProd' (ts : List Type) : Type :=
  match ts with
  | [] => Unit
  | t :: ts' => t × IteratedProd ts'

abbrev IteratedArrow (base : Type) (ts : List Type) : Type :=
  ts.foldr (· → ·) base

-- TODO what about the representation in the form of `IteratedProd (ts.map ...)`?

abbrev List.typesAllDecidableEq (ts : List Type) := ∀ ty ∈ ts, DecidableEq ty

abbrev List.typesAllHashable (ts : List Type) := ∀ ty ∈ ts, Hashable ty

abbrev List.typesAllFinEnum (ts : List Type) := ∀ ty ∈ ts, FinEnum ty

-- TODO deriving `Ord` for `IteratedProd` and `IteratedProd'`

instance instDecidableEqIteratedProd (inst : List.typesAllDecidableEq ts) : DecidableEq (IteratedProd ts) :=
  match ts with
  | [] => inferInstanceAs (DecidableEq Unit)
  | t :: ts' =>
    let : DecidableEq t := inst t (by simp)
    let inst' : List.typesAllDecidableEq ts' := fun ty h => inst ty (by simp ; exact Or.inr h)
    let := instDecidableEqIteratedProd inst'
    inferInstanceAs (DecidableEq (t × IteratedProd ts'))

instance instDecidableEqIteratedProd' (inst : List.typesAllDecidableEq ts) : DecidableEq (IteratedProd' ts) :=
  match ts with
  | [] => inferInstanceAs (DecidableEq Unit)
  | _ :: _ => instDecidableEqIteratedProd inst

instance instHashableIteratedProd (inst : List.typesAllHashable ts) : Hashable (IteratedProd ts) :=
  match ts with
  | [] => inferInstanceAs (Hashable Unit)
  | t :: ts' =>
    let : Hashable t := inst t (by simp)
    let inst' : List.typesAllHashable ts' := fun ty h => inst ty (by simp ; exact Or.inr h)
    let := instHashableIteratedProd inst'
    inferInstanceAs (Hashable (t × IteratedProd ts'))

instance instHashableIteratedProd' (inst : List.typesAllHashable ts) : Hashable (IteratedProd' ts) :=
  match ts with
  | [] => inferInstanceAs (Hashable Unit)
  | _ :: _ => instHashableIteratedProd inst

def IteratedProd.cartesianProduct (ts : List Type)
  -- slight lazy
  (elements : IteratedProd (ts.map (Unit → List ·))) : List (IteratedProd ts) :=
  match ts, elements with
  | [], _ => [()]
  | _ :: ts', (lis, elements) =>
    let res := IteratedProd.cartesianProduct ts' elements
    List.product (lis ()) res

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

-- TODO any existing way to define this kind of shortcutting comparison function?
-- TODO any way to avoid inserting such local proofs? will they affect performance?
def IteratedProd.patCmp {ts : List Type} {T : Type → Type}
  (cmp : ∀ {ty : Type} [DecidableEq ty], T ty → ty → Bool)
  (dec : List.typesAllDecidableEq ts)
  (po : IteratedProd (ts.map T)) (p : IteratedProd ts) : Bool :=
  match ts, po, p with
  | [], (), () => true
  | t :: _, (o, po'), (x, p') =>
    (@cmp _ (dec t (by simp)) o x)
    && IteratedProd.patCmp cmp (fun ty h => dec ty (by simp ; exact (Or.inr h))) po' p'

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
  (dec : List.typesAllDecidableEq fieldComponents)
  (favs : ⌞_ FieldUpdateDescr ⌟)
  (vbase : ⌞_ CanonicalField ⌟)
  (args : IteratedProd fieldComponents) : FieldBase :=
  favs.foldr (init := vbase.uncurry args) fun (fa, v) acc =>
    if fa.patCmp (fun o x => o.elim true (fun y => decide (y = x))) dec args
    then v.uncurry args
    else acc

class FieldRepresentation (FieldTypeConcrete : Type) where
  get : FieldTypeConcrete → ⌞_ CanonicalField ⌟
  set : ⌞_ FieldUpdateDescr ⌟ → FieldTypeConcrete → FieldTypeConcrete

class LawfulFieldRepresentation (FieldTypeConcrete : Type)
  (inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟) where
  get_set_idempotent :
    ∀ -- TODO not sure this should be made here in the argument, but using
      -- the fact that all `DecidableEq` instances are equal, this will not
      -- matter much?
      (dec : List.typesAllDecidableEq fieldComponents)
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
  (dec : List.typesAllDecidableEq fieldComponents) :
  (⌞_ FieldRepresentation ⌟) (⌞_ CanonicalField ⌟) where
  get := id
  set favs fc := IteratedArrow.curry (fieldUpdate dec favs fc)

instance canonicalFieldRepresentationLawful
  (dec : List.typesAllDecidableEq fieldComponents) :
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
  set : ∀ (dec : List.typesAllDecidableEq fieldComponents) favs cf,
    inst.get (inst.set favs (getBack cf)) = IteratedArrow.curry (fieldUpdate dec favs cf)

theorem FieldRepresentationEquivCanonical.set' {fieldComponents : List Type} {FieldBase : Type}
  {FieldTypeConcrete : Type}
  [inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟]
  {getBack : ⌞_ CanonicalField ⌟ → FieldTypeConcrete}
  (h : ⌞_ FieldRepresentationEquivCanonical FieldTypeConcrete inst getBack ⌟)
  (dec : List.typesAllDecidableEq fieldComponents) (favs fc) :
  getBack (IteratedArrow.curry (fieldUpdate dec favs (inst.get fc))) = inst.set favs fc := by
  have h1 := h.set dec favs (inst.get fc)
  rw [h.getBack_get_id] at h1 ; rw [← h1, h.getBack_get_id]

instance FieldRepresentationEquivCanonical.toLawful
  (FieldTypeConcrete : Type)
  (inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟)
  (getBack : ⌞_ CanonicalField ⌟ → FieldTypeConcrete)
  (dec : List.typesAllDecidableEq fieldComponents)
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

section HashSetOrMapAsField

-- HMM might be interesting to use a hybrid representation; e.g.,
-- a pair of hashset/map and a function

instance (priority := high + 1)
  : FieldRepresentation [] FieldBase FieldBase where
  get := id
  set favs fc := List.head? favs |>.elim fc Prod.snd

abbrev HashSetForIteratedProd {ts : List Type}
  (instd : List.typesAllDecidableEq ts)
  (insth : List.typesAllHashable ts) :=
  @Std.HashSet (IteratedProd ts)
    (@instBEqOfDecidableEq _ (instDecidableEqIteratedProd instd))
    (instHashableIteratedProd insth)

-- NOTE: It might be overly strong to require `FinEnum` here. In general,
-- a footprint can be computed from the `fieldUpdatePattern`, and we only
-- need to impose the finiteness condition on the footprint.
-- However, using `FinEnum` is much easier to implement, so we start with
-- it first.

-- CHECK will writing this in a recursive way, instead of constructing
-- all things to be (potentially) modified, be more efficient?

-- CHECK another chance to make things more efficient is to exploit
-- some properties of the description. for example, if the description
-- is `false`, then we only need to examine the entries that are already
-- in the hashset.
-- this might be related to how queries are optimized in database queries.

def HashSetForIteratedProd.update {ts : List Type}
  {instd : List.typesAllDecidableEq ts}
  {insth : List.typesAllHashable ts}
  (instfin : List.typesAllFinEnum ts)
  (fa : FieldUpdatePat ts)
  (v : CanonicalField ts Bool)
  (hs : HashSetForIteratedProd instd insth) : HashSetForIteratedProd instd insth :=
  sorry
  -- let prods := IteratedProd.cartesianProduct ts (fun ty h => @FinEnum.toList ty (instfin ty h))
  -- let mut hs := hs
  -- for p in prods do
  --   if !hs.contains p then
  --     hs := hs.insert p
  -- sorry

  -- (dec : List.typesAllDecidableEq ts)
  -- (favs : List (IteratedProd (List.map Option ts) × IteratedArrow FieldBase ts))

  -- (args : IteratedProd ts) : FieldBase :=
  -- favs.foldr (init := if hs.contains args then true else false) fun (fa, v) acc =>
  --   if fa.patCmp (fun o x => o.elim true (fun y => decide (y = x))) dec args
  --   then v.uncurry args
  --   else acc

-- NOTE: At the implementation level, usually there will be only one update
-- pattern and one value, so currently do not consider optimization for the
-- multiple patterns & values case.
-- TODO there are two ways of implementation: (1) `fold` and (2) `let mut` with loop.
-- which is faster? do both use the object linearly?
def HashSetForIteratedProd.updateMulti {ts : List Type}
  {instd : List.typesAllDecidableEq ts}
  {insth : List.typesAllHashable ts}
  (instfin : List.typesAllFinEnum ts)
  (favs : FieldUpdateDescr ts Bool)
  (hs : HashSetForIteratedProd instd insth) : HashSetForIteratedProd instd insth := Id.run do
  let mut res := hs
  for (fa, v) in favs do
    res := res.update instfin fa v
  return res

abbrev HashSetForIteratedProd' {ts : List Type}
  (instd : List.typesAllDecidableEq ts)
  (insth : List.typesAllHashable ts) :=
  @Std.HashSet (IteratedProd' ts)
    (@instBEqOfDecidableEq _ (instDecidableEqIteratedProd' instd))
    (instHashableIteratedProd' insth)

-- TODO this is very awkward ... due to the use of `IteratedArrow.curry`,
-- we cannot directly use `IteratedProd'` here
-- also, might also need to reflect on the interface of `get`; does it
-- introduce unnecessary overhead?
instance (priority := high)
  (instd : List.typesAllDecidableEq fieldComponents)
  (insth : List.typesAllHashable fieldComponents)
  (instfin : List.typesAllFinEnum fieldComponents)
  : FieldRepresentation fieldComponents Bool
  (HashSetForIteratedProd instd insth) where
  get fc := IteratedArrow.curry fun args => Std.HashSet.contains fc args
  set favs fc := fc.updateMulti instfin favs

#check Std.TreeSet

end HashSetOrMapAsField

-- section TreeSetOrMapAsField

-- instance (priority := high) : FieldRepresentation fieldComponents Bool
--   (Std.TreeSet (IteratedProd' fieldComponents)) where
--   get : FieldTypeConcrete → ⌞_ CanonicalField ⌟
--   set : ⌞_ FieldUpdateDescr ⌟ → FieldTypeConcrete → FieldTypeConcrete

-- #check Std.TreeSet

-- end TreeSetOrMapAsField

end SingleField

end Veil
