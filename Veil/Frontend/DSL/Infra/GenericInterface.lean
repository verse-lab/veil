import Std
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ProxyType
import Mathlib.Tactic.CongrExclamation
import Mathlib.Data.FinEnum
import Mathlib.Data.UInt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

section DataStructure

/-
There are multiple things:
- equality comparison (`BEq`? `DecidableEq`?)
- finiteness inheritance (`FinEnum`?) namely,
  how to relate the finiteness of (1) the state, (2) the state
  representation, (3) the transition system?
- hashability (`Hashable`?) and lawfulness (`LawfulHashable`?)
- the abilities above, and their time/space complexities

For comparison:
- `DecidableEq` might be impossible sometimes (e.g., when the data
  structure is too complicated)
- Sometimes it is possible for `Ext`-data structures, but might be
  expensive in time/space (for map, need to enumerate; for tree,
  need to pay extra price)
  - Usually in this case, the data structure is equivalent to
    the _underlying_ state
- Usually possible for some kind of `EquivBEq`
  - Usually in this case, the data structure is equivalent to
    the _underlying_ state _modulo this equivalence_

For finiteness:
- Usually inherited from the _underlying_ state through some kind
  of equivalence
- (We might care about this when we want to (1) enumerate states,
  or (2) state a correctness theorem that _directly_ involves the
  exhaustiveness of the state space)
  - CHECK If we do not, what can we do? Is there any "refinement" there?

For hashability:
- Kind of orthogonal to the above two; lawfulness is usually
  feasible. The key is the complexity (incremental?)

-/

-- just playing. maybe the following is all trivial

class FinsetLike (β : Type v) [Membership α β] where
  insert : (a : α) → (b : β) → a ∉ b → β
  erase : (a : α) → (b : β) → a ∈ b → β

/-
class FinsetLikeEnumerate (β : Type v) [Membership α β] [inst : FinsetLike β] where
  enumerate : β → Finset α
  enumerate_mem_iff : ∀ (a : α) (b : β), a ∈ b ↔ a ∈ enumerate b

class LawfulFinsetLike /- (α : outParam (Type u)) -/ (β : Type v)
  [Membership α β] [inst : FinsetLike β] [DecidableEq α] where
  insert_mem_iff : ∀ (a : α) (b : β) (h : a ∉ b),
    ∀ x, x ∈ inst.insert a b h ↔ x = a ∨ x ∈ b
  erase_mem_iff : ∀ (a : α) (b : β) (h : a ∈ b),
    ∀ x, x ∈ inst.erase a b h ↔ x ≠ a ∧ x ∈ b
-/

class LawfulFinsetLike /- (α : outParam (Type u)) -/ (β : Type v)
  [Membership α β] [inst : FinsetLike β] [DecidableEq α] where
  toFinset : β → Finset α
  toFinset_mem_iff : ∀ (a : α) (b : β), a ∈ b ↔ a ∈ toFinset b
  insert_toFinset :
    ∀ (a : α) (b : β) (h : a ∉ b), toFinset (inst.insert a b h) = insert a (toFinset b)
  erase_toFinset :
    ∀ (a : α) (b : β) (h : a ∈ b), toFinset (inst.erase a b h) = (toFinset b).erase a

class HashAsAddCommGroup (α : Type u) (ι : Type w) where
  op : α → ι

instance [Hashable α] : HashAsAddCommGroup α UInt64 where
  op := hash

-- TODO maybe adapt this to map structures as well, later
-- "lifting" a data structure to allow hashing while updating
-- (i.e., incremental hashing)

-- CAVEAT: `β × UInt64` is not enough; it does not carry any invariant
-- that is required for proving the `LawfulHashable` of the whole thing;
-- to maintain this invariant, need `LawfulFinsetLike`
-- CAVEAT: the update of `hashval` depends on the membership, so need to
-- do something about this
structure HashCompanioned (β : Type v) (ι : Type w)
  [DecidableEq α] [Membership α β]
  [FinsetLike β] [LawfulFinsetLike β]
  [AddCommGroup ι] [insth : HashAsAddCommGroup α ι] where
  inner : β
  hashval : ι
  invariant : hashval = (∑ a ∈ LawfulFinsetLike.toFinset inner, insth.op a)

section HashCompanioned

variable {α : Type u} {β : Type v} {ι : Type w}
  [DecidableEq α] [Membership α β]
  [FinsetLike β] [instl : LawfulFinsetLike β]
  [AddCommGroup ι] [insth : HashAsAddCommGroup α ι]

instance : Membership α (HashCompanioned β ι) where
  mem b a := a ∈ b.inner

def HashCompanioned.insert (a : α) (b : HashCompanioned β ι) (h : a ∉ b) : HashCompanioned β ι :=
  { inner := FinsetLike.insert a b.inner h
    hashval := HashAsAddCommGroup.op a + b.hashval
    invariant := by
      rw [b.invariant, instl.insert_toFinset]
      have h' : a ∉ instl.toFinset b.inner := by rw [← instl.toFinset_mem_iff] ; exact h
      rw [Finset.sum_insert' (M := ι) h']
  }

def HashCompanioned.erase (a : α) (b : HashCompanioned β ι) (h : a ∈ b) : HashCompanioned β ι :=
  { inner := FinsetLike.erase a b.inner h
    hashval := b.hashval - HashAsAddCommGroup.op a
    invariant := by
      rw [b.invariant, instl.erase_toFinset]
      have h' : a ∈ instl.toFinset b.inner := by rw [← instl.toFinset_mem_iff] ; exact h
      rw [Finset.sum_erase_eq_sub h']
  }

instance : FinsetLike (HashCompanioned β ι) where
  insert := HashCompanioned.insert
  erase := HashCompanioned.erase

-- an easy lift
instance : LawfulFinsetLike (HashCompanioned β ι) where
  toFinset b := instl.toFinset b.inner
  toFinset_mem_iff a b := instl.toFinset_mem_iff a b.inner
  insert_toFinset a b h := instl.insert_toFinset a b.inner h
  erase_toFinset a b h := instl.erase_toFinset a b.inner h

instance [Hashable α] : Hashable (HashCompanioned β UInt64) where
  hash := HashCompanioned.hashval

instance : β ≃ HashCompanioned β ι where
  toFun b := { inner := b, hashval := (∑ a ∈ LawfulFinsetLike.toFinset b, insth.op a), invariant := rfl }
  invFun b := b.inner
  left_inv b := rfl
  right_inv b := by dsimp ; rcases b with ⟨i, h, inv⟩ ; subst h ; congr

-- `LawfulHashable` should be derivable from some weaker `BEq`,
-- not necessarily `DecidableEq`, especially there is no well-defined
-- `DecidableEq`
variable [DecidableEq β] [DecidableEq ι]

instance : DecidableEq (HashCompanioned β ι) :=
  fun a b =>
    let ⟨i1, h1, inv1⟩ := a
    let ⟨i2, h2, inv2⟩ := b
    let q : Decidable (i1 = i2) := inferInstance
    match q with
    | isTrue _ =>
      let qq : Decidable (h1 = h2) := inferInstance
      match qq with
      | isTrue _ => isTrue (by grind)
      | isFalse _ => isFalse (by grind)
    | isFalse _ => isFalse (by grind)

-- for `DecidableEq`, this is free
instance [Hashable α] : LawfulHashable (HashCompanioned β UInt64) :=
  inferInstance

end HashCompanioned

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

section FinsetLikeInstances

variable {α : Type u}

instance [BEq α] [Hashable α] : FinsetLike (Std.HashSet α) where
  insert a b _ := b.insert a
  erase a b _ := b.erase a

instance {cmp : α → α → Ordering} : FinsetLike (Std.TreeSet α cmp) where
  insert a b _ := b.insert a
  erase a b _ := b.erase a

end FinsetLikeInstances

section LawfulFinsetLikeInstances

variable {α : Type u}

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

end LawfulFinsetLikeInstances





-- NOTE: We should be able to unify partial `FinmapLike` and `FinsetLike`,
-- but for total map, we need a different interface.

class TotalMapLike (α : outParam (Type u)) (β : outParam (Type v)) (γ : Type w) where
  get : γ → α → β
  insert : α → β → γ → γ

class LawfulTotalMapLike /- (α : outParam (Type u)) (β : outParam (Type v)) -/ (γ : Type w)
  [inst : TotalMapLike α β γ] [DecidableEq α] where
  insert_get : ∀ (a a' : α) (b : β) (mp : γ),
    inst.get (inst.insert a b mp) a' = if a = a' then b else inst.get mp a'

abbrev ArrayAsTotalMap (n : Nat) (β : Type v) :=
  { mp : Array β // n = mp.size }

instance [Inhabited β] : Inhabited (ArrayAsTotalMap n β) :=
  ⟨⟨Array.replicate n default, Eq.symm Array.size_replicate⟩⟩

abbrev TotalHashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] :=
  { mp : Std.HashMap α β // ∀ a, a ∈ mp }

instance [FinEnum α] [DecidableEq α] [Hashable α] [LawfulHashable α] [Inhabited β] : Inhabited (TotalHashMap α β) :=
  ⟨⟨Std.HashMap.ofList ((FinEnum.toList α).map (fun a => (a, default))),
    by intro a ; rw [Std.HashMap.mem_ofList, List.map_map] ; unfold Function.comp ; simp⟩⟩

abbrev TotalTreeMap (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare) :=
  { mp : Std.TreeMap α β cmp // ∀ a, a ∈ mp }

instance {cmp : α → α → Ordering} [FinEnum α] [Std.LawfulEqCmp cmp] [Std.TransCmp cmp] [DecidableEq α] [Inhabited β] : Inhabited (TotalTreeMap α β cmp) :=
  ⟨⟨Std.TreeMap.ofList ((FinEnum.toList α).map (fun a => (a, default))) cmp,
    by intro a ; rw [Std.TreeMap.mem_ofList, List.map_map] ; unfold Function.comp ; simp⟩⟩

section TotalMapLikeInstances

variable {β : Type v}

instance : TotalMapLike (Fin n) β (ArrayAsTotalMap n β) where
  get mp a := mp.val[a.val]'(mp.property ▸ a.prop)
  insert a b mp := ⟨mp.val.set a.val b (mp.property ▸ a.prop),
    (Eq.symm (Array.size_set (xs := mp.val) (i := a.val) (mp.property ▸ a.prop))) ▸ mp.prop⟩

variable {α : Type u}

instance [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] : TotalMapLike α β (TotalHashMap α β) where
  get mp a := mp.val[a]'(mp.property a)
  insert a b mp := ⟨mp.val.insert a b,
    fun a => Std.HashMap.mem_insert.mpr (Or.inr (mp.property a))⟩

instance {cmp : α → α → Ordering} [Std.TransCmp cmp] : TotalMapLike α β (TotalTreeMap α β cmp) where
  get mp a := mp.val[a]'(mp.property a)
  insert a b mp := ⟨mp.val.insert a b,
    fun a => Std.TreeMap.mem_insert.mpr (Or.inr (mp.property a))⟩

end TotalMapLikeInstances

section LawfulTotalMapLikeInstances

variable {β : Type v}

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

end LawfulTotalMapLikeInstances






end DataStructure

-- NOTE: Currently, the following does not consider universe polymorphism.

section Iterated

-- TODO I believe this kind of things must have been formalized & proved
-- before. find them!

abbrev IteratedProd (ts : List Type) : Type :=
  ts.foldr Prod Unit

def IteratedProd' (ts : List Type) : Type :=
  match ts with
  | [] => Unit
  | [t] => t
  | t :: ts' => t × IteratedProd' ts'

def IteratedProd.toIteratedProd' {ts : List Type}
  (a : IteratedProd ts) : IteratedProd' ts :=
  match ts, a with
  | [], _ => ()
  | [_], (x, _) => x
  | _ :: _ :: _, (x, xs) => (x, IteratedProd.toIteratedProd' xs)

def IteratedProd.ofIteratedProd' {ts : List Type}
  (a : IteratedProd' ts) : IteratedProd ts :=
  match ts, a with
  | [], _ => ()
  | [_], x => (x, ())
  | _ :: _ :: _, (x, xs) => (x, IteratedProd.ofIteratedProd' xs)

def IteratedProd'.equiv {ts : List Type} : IteratedProd ts ≃ IteratedProd' ts where
  toFun := IteratedProd.toIteratedProd'
  invFun := IteratedProd.ofIteratedProd'
  left_inv := by
    simp [Function.LeftInverse]
    induction ts with
    | nil => intros ; rfl
    | cons t ts ih =>
      rintro ⟨x, xs⟩ ; rcases ts with _ | ⟨_, _⟩ <;> try rfl
      simp [IteratedProd.toIteratedProd', IteratedProd.ofIteratedProd'] ; apply ih
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse]
    induction ts with
    | nil => intros ; rfl
    | cons t ts ih =>
      intro a ; rcases ts with _ | ⟨_, _⟩ <;> try rfl
      rcases a with ⟨x, xs⟩
      simp [IteratedProd.toIteratedProd', IteratedProd.ofIteratedProd'] ; congr 1 ; apply ih

abbrev IteratedArrow (codomain : Type) (ts : List Type) : Type :=
  ts.foldr (· → ·) codomain

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

def IteratedArrow.curry {codomain : Type} {ts : List Type}
  (k : (IteratedProd ts) → codomain) : IteratedArrow codomain ts :=
  match ts with
  | [] => k ()
  | t :: _ =>
    fun (x : t) => IteratedArrow.curry (fun xs => k (x, xs))

def IteratedArrow.uncurry {codomain : Type} {ts : List Type}
  (f : IteratedArrow codomain ts) (args : IteratedProd ts) : codomain :=
  match ts, f, args with
  | [], f, () => f
  | _ :: _, f, (x, xs) => IteratedArrow.uncurry (f x) xs

theorem IteratedArrow.curry_uncurry {codomain : Type} {ts : List Type}
  (a : IteratedArrow codomain ts) :
  IteratedArrow.curry (fun args => a.uncurry args) = a := by
  induction ts with
  | nil => simp [IteratedArrow.curry, IteratedArrow.uncurry]
  | cons t ts ih =>
    simp [IteratedArrow.curry, IteratedArrow.uncurry]
    funext x ; specialize ih (a x) ; rw [ih]

theorem IteratedArrow.uncurry_curry {codomain : Type} {ts : List Type}
  (k : (IteratedProd ts) → codomain) :
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
  (codomain : T₂ Unit)
  (prod : ∀ {tya tyb : Type}, T₁ tya → T₂ tyb → T₂ (tya × tyb))
  (elements : IteratedProd (ts.map T₁)) : T₂ (IteratedProd ts) :=
  match ts, elements with
  | [], _ => codomain
  | _ :: _, (lis, elements) => prod lis <| IteratedProd.fold codomain prod elements

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

-- NOTE: this should have some effect like deforestation, compared to using
-- `cartesianProduct` directly
-- TODO this might be too ... specific? or for monad?
def IteratedProd.foldMap {α : Type} {ts : List Type}
  (init : α) (f : IteratedArrow (α → α) ts)
  (elements : IteratedProd <| ts.map (Unit → List ·)) : α :=
  match ts, elements with
  | [], _ => f init
  | _ :: _, (lis, elements) =>
    let liss := lis ()
    liss.foldl (init := init) fun a b =>
      IteratedProd.foldMap a (f b) elements

theorem IteratedProd.foldMap_eq_cartesianProduct {α : Type} {ts : List Type}
  (init : α) (f : IteratedArrow (α → α) ts) (g : α → IteratedProd ts → α)
  (eq : ∀ a p, f.uncurry p a = g a p)
  (elements : IteratedProd <| ts.map (Unit → List ·)) :
  IteratedProd.foldMap init f elements =
    elements.cartesianProduct.foldl (init := init) g := by
  induction ts generalizing init with
  | nil => simp [IteratedProd.foldMap, IteratedProd.cartesianProduct, IteratedProd.fold] ; apply eq
  | cons t ts ih =>
    rcases elements with ⟨lis, elements⟩
    simp [IteratedProd.foldMap, IteratedProd.cartesianProduct, IteratedProd.fold, ih]
    generalize (fold [()] (fun {tya tyb} x => (x ()).product) elements) = subprods
    generalize (lis ()) = lis'
    clear *- eq
    -- is this induction actually needed? or use some theorem?
    induction lis' generalizing init with
    | nil => rfl
    | cons x lis' ih => simp [List.product, ih, List.foldl_map, ← eq] ; rfl

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

instance instHashableIteratedProd (inst : List.typesAll Hashable ts) :
  Hashable (IteratedProd ts) :=
    inst.toIteratedProd.fold (inferInstanceAs (Hashable Unit)) (@instHashableProd)

end ListTypeAll

section IteratedProdInstances

macro "infer_instance_for_iterated_prod" : tactic =>
  `(tactic| repeat' (first | infer_instance | constructor ))

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

/-
-- NOTE: this is not used, so commenting out for now
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
-/

-- this is problematic; the equivalence holds only when the domain
-- of the `ExtHashMap` is full
/-
abbrev HashMapForIteratedProd (ts : List Type)
  [instd : DecidableEq (IteratedProd ts)]
  [insth : Hashable (IteratedProd ts)] (codomain : Type) := Std.HashMap (IteratedProd ts) codomain

instance instHashMapForIteratedProdEquivIteratedArrow :
  HashMapForIteratedProd ts codomain ≃ IteratedArrow codomain ts where
-/

end HashMapAndSet

end Iterated

section SingleField

variable (fieldDomain : List Type) (FieldCodomain : Type)

local macro "⌞" t1:ident t2:ident* "⌟" : term => `($t1 $(Lean.mkIdent `fieldDomain) $t2:ident*)
local macro "⌞_" t1:ident t2:ident* "⌟" : term => `(⌞ $t1 $(Lean.mkIdent `FieldCodomain) $t2:ident* ⌟)

abbrev FieldUpdatePat : Type := IteratedProd (fieldDomain.map Option)

abbrev CanonicalField : Type := IteratedArrow FieldCodomain fieldDomain

abbrev FieldUpdateDescr := List (⌞ FieldUpdatePat ⌟ × ⌞_ CanonicalField ⌟)

def FieldUpdatePat.pad (n : Nat) : IteratedArrow (FieldUpdatePat fieldDomain)
    (fieldDomain.take n |>.map Option) :=
  IteratedArrow.curry fun args => (by
    let res := args ++ IteratedProd.default (ts := fieldDomain.drop n) (@Option.none)
    simp at res
    exact res)

def FieldUpdatePat.match
  {fieldDomain : List Type}
  (dec : IteratedProd (fieldDomain.map DecidableEq))
  (fa : FieldUpdatePat fieldDomain) args :=
  IteratedProd.patCmp (fun o x => o.elim true (fun y => decide (y = x))) dec fa args

def FieldUpdateDescr.fieldUpdate
  {fieldDomain : List Type}
  {FieldCodomain : Type}
  (dec : IteratedProd (fieldDomain.map DecidableEq))
  (favs : ⌞_ FieldUpdateDescr ⌟)
  (vbase : ⌞_ CanonicalField ⌟)
  (args : IteratedProd fieldDomain) : FieldCodomain :=
  favs.foldr (init := vbase.uncurry args) fun (fa, v) acc => if fa.match dec args then v.uncurry args else acc

def FieldUpdatePat.footprintRaw
  {fieldDomain : List Type}
  (instfin : IteratedProd (fieldDomain.map FinEnum))
  (fa : FieldUpdatePat fieldDomain) :=
  instfin.zipWith fa fun fin b =>
    b.elim (fun (_ : Unit) => fin.toList _) (fun x _ => [x])

theorem FieldUpdatePat.footprint_match_iff
  {fieldDomain : List Type}
  (instfin : IteratedProd (fieldDomain.map FinEnum))
  (dec : IteratedProd (fieldDomain.map DecidableEq))
  {fa : FieldUpdatePat fieldDomain} :
  ∀ args, args ∈ (fa.footprintRaw instfin).cartesianProduct ↔ fa.match dec args := by
  intro args
  induction fieldDomain
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
abbrev FieldRepresentation.setSingle {fieldDomain : List Type}
  {FieldCodomain FieldTypeConcrete : Type}
  [self : ⌞_ FieldRepresentation FieldTypeConcrete ⌟]
  (fa : ⌞ FieldUpdatePat ⌟) (v : ⌞_ CanonicalField ⌟) (fc : FieldTypeConcrete) : FieldTypeConcrete :=
  self.set [(fa, v)] fc

-- TODO can this be declared as `instance`?
def FieldRepresentation.mkFromSingleSet {fieldDomain : List Type}
  {FieldCodomain : Type} {FieldTypeConcrete : Type}
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

theorem LawfulFieldRepresentationSet.mkFromSingleSet {fieldDomain : List Type}
  {FieldCodomain : Type} {FieldTypeConcrete : Type}
  (get : FieldTypeConcrete → ⌞_ CanonicalField ⌟)
  (setSingle : ⌞ FieldUpdatePat ⌟ → ⌞_ CanonicalField ⌟ → FieldTypeConcrete → FieldTypeConcrete) :
  (⌞_ LawfulFieldRepresentationSet FieldTypeConcrete ⌟)
    (FieldRepresentation.mkFromSingleSet get setSingle) where
  set_append := by
    introv ; simp [FieldRepresentation.mkFromSingleSet, FieldRepresentation.set]
  set_nil := by
    introv ; simp [FieldRepresentation.mkFromSingleSet, FieldRepresentation.set]

def CanonicalField.set {fieldDomain : List Type} {FieldCodomain : Type}
  (dec : IteratedProd (fieldDomain.map DecidableEq))
  (favs : ⌞_ FieldUpdateDescr ⌟)
  (fc : ⌞_ CanonicalField ⌟) : ⌞_ CanonicalField ⌟ :=
  IteratedArrow.curry (favs.fieldUpdate dec fc)

class LawfulFieldRepresentation (FieldTypeConcrete : Type)
  (inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟)
  extends ⌞_ LawfulFieldRepresentationSet FieldTypeConcrete inst ⌟ where
  get_set_idempotent :
    ∀ -- TODO not sure this should be made here in the argument, but using
      -- the fact that all `DecidableEq` instances are equal, this will not
      -- matter much?
      (dec : IteratedProd (fieldDomain.map DecidableEq))
      (fc : FieldTypeConcrete) fav,
      inst.get (inst.set [fav] fc) = (inst.get fc).set dec [fav]
  -- NOTE: temporarily disabling this law, since it is not used
  -- set_get_idempotent :
  --   ∀ (fc : FieldTypeConcrete) (fa : FieldUpdatePat fieldDomain),
  --     inst.set [(fa, inst.get fc)] fc = fc

instance canonicalFieldRepresentation {fieldDomain : List Type} {FieldCodomain : Type}
  (dec : IteratedProd (fieldDomain.map DecidableEq)) :
  (⌞_ FieldRepresentation ⌟) (⌞_ CanonicalField ⌟) where
  get := id
  set favs fc := fc.set dec favs

instance canonicalFieldRepresentationLawful
  (dec : IteratedProd (fieldDomain.map DecidableEq)) :
  LawfulFieldRepresentation fieldDomain FieldCodomain (⌞_ CanonicalField ⌟)
    -- TODO why synthesis fails here? is it because there is no `semiOutParam`, `outParam` or because of `dec`?
    -- also, due to the synthesis failure, `inst` cannot be declared using `[]`
    (inst := canonicalFieldRepresentation dec) where
  get_set_idempotent := by
    introv ; simp [FieldRepresentation.get, FieldRepresentation.set]
    congr ; apply IteratedProd.map_DecidableEq_eq
  -- set_get_idempotent := by
  --   introv ; simp +unfoldPartialApp [CanonicalField.set, FieldUpdateDescr.fieldUpdate, FieldRepresentation.set, FieldRepresentation.get, IteratedArrow.curry_uncurry]
  set_append := by
    introv ; simp +unfoldPartialApp [CanonicalField.set, FieldUpdateDescr.fieldUpdate, FieldRepresentation.set, IteratedArrow.uncurry_curry]
  set_nil := by
    introv ; simp +unfoldPartialApp [CanonicalField.set, FieldRepresentation.set, FieldUpdateDescr.fieldUpdate, IteratedArrow.curry_uncurry]

/-- Strengthen `get_set_idempotent` to `FieldUpdateDescr`. -/
theorem LawfulFieldRepresentation.get_set_idempotent' {fieldDomain : List Type} {FieldCodomain : Type}
  {FieldTypeConcrete : Type}
  {inst : ⌞_ FieldRepresentation FieldTypeConcrete ⌟}
  (inst2 : ⌞_ LawfulFieldRepresentation FieldTypeConcrete inst ⌟)
  (dec : IteratedProd (fieldDomain.map DecidableEq)) favs fc :
    inst.get (inst.set favs fc) = (inst.get fc).set dec favs := by
  induction favs with
  | nil => simp +unfoldPartialApp [inst2.set_nil, CanonicalField.set,
    FieldUpdateDescr.fieldUpdate, IteratedArrow.curry_uncurry]
  | cons fav favs ih =>
    have tmp := inst2.set_append favs [fav]
    simp at tmp ; rw [← tmp, inst2.get_set_idempotent dec, ih]
    apply (canonicalFieldRepresentationLawful _ _ dec).set_append

section FieldRepresentationInstances

instance (priority := high + 1)
  : FieldRepresentation [] FieldCodomain FieldCodomain where
  get := id
  set favs fc := List.head? favs |>.elim fc Prod.snd

instance (priority := high + 1)
  : LawfulFieldRepresentation [] FieldCodomain FieldCodomain inferInstance where
  set_nil := by introv ; simp [FieldRepresentation.set]
  set_append := by
    introv ; simp [FieldRepresentation.set]
    rcases favs₂ with _ | ⟨fav₂, _⟩ <;> simp
  get_set_idempotent := by introv ; rfl

-- CHECK It might be interesting to use a hybrid representation; e.g.,
-- mixing the use of hashmap and function? For a fully map representation,
-- it might take a lot of space, although the access is fast; for the
-- function representation, it might be slow to access (when the closure
-- is deep), but it allows a smaller "description" which might result in
-- fast computation of the target value and small space usage.

-- CHECK another chance to make things more efficient is to exploit
-- some properties of the description. for example, if the description
-- is `false`, then we only need to examine the entries that are already
-- in the hashset.
-- this might be related to how queries are optimized in database queries.

-- NOTE: It might be overly strong to require `FinEnum` here. In general,
-- a footprint can be computed from the `fieldUpdatePattern`, and we only
-- need to impose the finiteness condition on the footprint.

section FinsetLike

omit fieldDomain FieldCodomain

variable {fieldDomain : List Type}
  [instd : DecidableEq α]
  [instm : Membership α β]
  [inst : FinsetLike β]
  [instl : LawfulFinsetLike β]
  [instdm : DecidableRel instm.mem]
  (equiv : IteratedProd fieldDomain ≃ α)
  (instfin : IteratedProd (fieldDomain.map FinEnum))

def FieldRepresentation.Finset.setSingle
  (fa : FieldUpdatePat fieldDomain)
  (v : CanonicalField fieldDomain Bool) (fc : β) :=
  inst.batchUpdate
    ((fa.footprintRaw instfin).cartesianProduct.map equiv) (v.uncurry ∘ equiv.symm) fc

def FieldRepresentation.Finset.setSingle'
  (fa : FieldUpdatePat fieldDomain)
  (v : CanonicalField fieldDomain Bool) (fc : β) :=
  let vv := v.uncurry
  IteratedProd.foldMap fc (IteratedArrow.curry fun arg fc' =>
    inst.update (equiv arg) (vv arg) fc') (fa.footprintRaw instfin)

omit instd instl in
theorem FieldRepresentation.Finset.setSingle_eq fa v (fc : β) :
  setSingle equiv instfin fa v fc = setSingle' equiv instfin fa v fc := by
  unfold setSingle setSingle'
  simp [FinsetLike.batchUpdate_eq_foldl_update, IteratedProd.foldMap_eq_cartesianProduct, IteratedArrow.uncurry_curry,
    List.foldl_map, Function.comp_apply]

instance instFinsetLikeAsFieldRep : FieldRepresentation fieldDomain Bool β :=
  FieldRepresentation.mkFromSingleSet
    (get := fun fc => IteratedArrow.curry (instm.mem fc ∘ equiv))
    (setSingle := FieldRepresentation.Finset.setSingle' equiv instfin)

-- hope this does not introduce any trouble
open Classical in
instance instFinsetLikeLawfulFieldRep : LawfulFieldRepresentation fieldDomain Bool β
    -- TODO this is awkward; synthesis fails here, and the `equiv.symm` is weird
    (instFinsetLikeAsFieldRep equiv instfin) where
  toLawfulFieldRepresentationSet :=
    LawfulFieldRepresentationSet.mkFromSingleSet ..
  get_set_idempotent := by
    introv ; rcases fav with ⟨fa, v⟩
    simp +unfoldPartialApp [instFinsetLikeAsFieldRep, FieldRepresentation.mkFromSingleSet,
      CanonicalField.set, FieldRepresentation.set, FieldRepresentation.Finset.setSingle',
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

end FinsetLike

section TotalMapLike

omit fieldDomain FieldCodomain

variable {fieldDomain : List Type} {FieldCodomain : Type}
  [instd : DecidableEq α]
  [inst : TotalMapLike α FieldCodomain γ]
  [instl : LawfulTotalMapLike γ]
  (equiv : IteratedProd fieldDomain ≃ α)
  (instfin : IteratedProd (fieldDomain.map FinEnum))

def FieldRepresentation.TotalMapLike.setSingle'
  (fa : FieldUpdatePat fieldDomain)
  (v : CanonicalField fieldDomain FieldCodomain) (fc : γ) :=
  let vv := v.uncurry
  IteratedProd.foldMap fc (IteratedArrow.curry fun arg fc' =>
    inst.insert (equiv arg) (vv arg) fc') (fa.footprintRaw instfin)

instance instTotalMapLikeAsFieldRep : FieldRepresentation fieldDomain FieldCodomain γ :=
  FieldRepresentation.mkFromSingleSet
    (get := fun fc => IteratedArrow.curry (inst.get fc ∘ equiv))
    (setSingle := FieldRepresentation.TotalMapLike.setSingle' equiv instfin)

open Classical in
instance instTotalMapLikeLawfulFieldRep : LawfulFieldRepresentation fieldDomain FieldCodomain γ
    -- TODO this is awkward; synthesis fails here, and the `equiv.symm` is weird
    (instTotalMapLikeAsFieldRep equiv instfin) where
  toLawfulFieldRepresentationSet :=
    LawfulFieldRepresentationSet.mkFromSingleSet ..
  get_set_idempotent := by
    -- TODO this proof seems repetitive
    introv ; rcases fav with ⟨fa, v⟩
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

end TotalMapLike

end FieldRepresentationInstances

-- section TreeSetOrMapAsField

-- instance (priority := high) : FieldRepresentation fieldDomain Bool
--   (Std.TreeSet (IteratedProd' fieldDomain)) where
--   get : FieldTypeConcrete → ⌞_ CanonicalField ⌟
--   set : ⌞_ FieldUpdateDescr ⌟ → FieldTypeConcrete → FieldTypeConcrete

-- #check Std.TreeSet

-- end TreeSetOrMapAsField

end SingleField

end Veil
