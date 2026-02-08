import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.FinEnum
import Veil.Frontend.DSL.Module.Names
import Veil.Util.Deriving
import Mathlib.Tactic.DeriveFintype
import Std.Data.TreeSet.Lemmas
import Std.Data.ExtTreeSet.Lemmas

/-! # Reification of Types of State Fields -/

namespace Veil

section IteratedProd

/-- This always has a `Unit` at the end. -/
abbrev IteratedProd (ts : List Type) : Type :=
  ts.foldr Prod Unit

def IteratedProd.default {ts : List Type} {T : Type → Type} (default : ∀ (ty : Type), T ty) : IteratedProd (ts.map T) :=
  match ts with
  | [] => ()
  | t :: _ => (default t, IteratedProd.default default)

def IteratedProd.singleton {t : Type} (a : t) : IteratedProd [t] := (a, ())

def IteratedProd.nth {ts : List Type} (i : Fin ts.length) (a : IteratedProd ts) : ts[i] :=
  match ts, i with
  | _ :: _, ⟨0, _⟩ => a.fst
  | _ :: _, ⟨Nat.succ i, h⟩ => IteratedProd.nth ⟨i, Nat.le_of_succ_le_succ h⟩ a.snd

def IteratedProd.append {ts1 ts2 : List Type}
  (p1 : IteratedProd ts1) (p2 : IteratedProd ts2) : IteratedProd (ts1 ++ ts2) :=
  match ts1, p1 with
  | [], _ => p2
  | _ :: _, (a, p1) => (a, IteratedProd.append p1 p2)

instance : HAppend (IteratedProd ts1) (IteratedProd ts2) (IteratedProd (ts1 ++ ts2)) where
  hAppend := IteratedProd.append

/-- Not sure if this is actually "fold". -/
def IteratedProd.fold {ts : List Type} {T₁ : Type → Type} {T₂ : Type → Sort u}
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

def IteratedProd.zip {ts : List Type} {T₁ T₂ : Type → Type}
  (elements₁ : IteratedProd (ts.map T₁))
  (elements₂ : IteratedProd (ts.map T₂)) :=
  IteratedProd.zipWith elements₁ elements₂ Prod.mk

def IteratedProd.zipWithM [Monad m] {ts : List Type} {T₁ T₂ T₃ : Type → Type}
  (elements₁ : IteratedProd (ts.map T₁))
  (elements₂ : IteratedProd (ts.map T₂))
  (zip : ∀ {ty : Type}, T₁ ty → T₂ ty → m (T₃ ty)) : m (IteratedProd (ts.map T₃)) := do
  match ts, elements₁, elements₂ with
  | [], _, _ => pure ()
  | _ :: _, (e₁, elements₁), (e₂, elements₂) =>
    let e ← zip e₁ e₂
    let elements ← IteratedProd.zipWithM elements₁ elements₂ zip
    pure (e, elements)

-- TODO does this really implement lazy & cacheable evaluation?
def IteratedProd.cartesianProduct {ts : List Type}
  (elements : IteratedProd (ts.map (Unit → List ·))) :=
  IteratedProd.fold [()] (List.product <| · ()) elements

end IteratedProd

section EfficientIteratedProd

/-- A slightly more efficient representation of `IteratedProd` that does not
have a `Unit` at the end. -/
abbrev IteratedProd' (ts : List Type) : Type :=
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
      simp [IteratedProd.toIteratedProd', IteratedProd.ofIteratedProd'] ; apply ih

end EfficientIteratedProd

section IteratedArrow

abbrev IteratedArrow (codomain : Type) (ts : List Type) : Type :=
  ts.foldr (· → ·) codomain

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

end IteratedArrow

section IteratedProd

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
    induction lis' generalizing init with
    | nil => rfl
    | cons x lis' ih => simp [List.product, ih, List.foldl_map, ← eq] ; rfl

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

macro "infer_instance_for_iterated_prod" : tactic =>
  `(tactic| repeat' (first | infer_instance | constructor ))

open Lean in
macro "dsimp_state_representation" : tactic =>
  `(tactic| (try dsimp only [$fieldConcreteDispatcher:ident]) <;> (try dsimp only [$fieldAbstractDispatcher:ident]) <;>
   (try dsimp only [$instFieldRepresentation:ident]) <;> (try dsimp only [$instAbstractFieldRepresentation:ident]) <;>
   (try dsimp only [$(mkIdent ``IteratedProd'):ident, $(mkIdent `State.Label.toDomain):ident, $(mkIdent `State.Label.toCodomain):ident, $(mkIdent ``id):ident]) <;>
   (try dsimp))
open Lean in
macro "infer_instance_for_iterated_prod'" : tactic =>
  `(tactic| dsimp_state_representation <;> infer_instance)

end IteratedProd

section Enumeration

/-- The `FinEnum` in Mathlib might be good for proving, but for execution
it might be very inefficient. This alternative is centered around `List`s
that enumerate all values. -/
class Enumeration (α : Type u) where
  allValues : List α
  complete : ∀ a : α, a ∈ allValues

def Enumeration.ofEquiv (α : Type u) {β : Type v} [inst : Enumeration α] (h : α ≃ β) : Enumeration β where
  allValues := inst.allValues.map h
  complete := by simp ; intro b ; exists (h.symm b) ; simp ; apply inst.complete

attribute [grind ←] Enumeration.complete

instance (priority := high) [enum : Enumeration α] [DecidableEq α] : FinEnum α := FinEnum.ofList enum.allValues enum.complete
/-!
Here only gives some basic instances. More complicated ones should be
found in `Veil.Frontend.Std`.
-/

instance : Enumeration Empty where
  allValues := []
  complete := by simp

instance : Enumeration PUnit where
  allValues := [PUnit.unit]
  complete := by simp

instance : Enumeration Bool where
  allValues := [true, false]
  complete := by simp

instance {n : Nat} : Enumeration (Fin n) where
  allValues := List.finRange n
  complete := by simp

instance [inst : Enumeration α] : Enumeration (Option α) where
  allValues := none :: inst.allValues.map some
  complete := by intro x ; rcases x <;> grind

instance {α β} [insta : Enumeration α] [instb : Enumeration β] : Enumeration (α × β) where
  allValues := List.product insta.allValues instb.allValues
  complete := by simp ; grind

instance {α β} [insta : Enumeration α] [instb : Enumeration β] : Enumeration (Sum α β) where
  allValues := (insta.allValues.map Sum.inl) ++ (instb.allValues.map Sum.inr)
  complete := by simp ; grind

instance [inst : Enumeration α] (p : α → Prop) [DecidablePred p] : Enumeration { x // p x } where
  allValues := inst.allValues.filterMap fun x => if h : p x then some ⟨x, h⟩ else none
  complete := by simp ; grind

instance {β : α → Type v} [insta : Enumeration α] [instb : ∀ a, Enumeration (β a)] : Enumeration (Sigma β) where
  allValues := insta.allValues.flatMap fun a => (instb a).allValues.map <| Sigma.mk a
  complete := by simp ; grind

def Enumeration.Pi.enum [insta : Enumeration α] [DecidableEq α] (β : α → Type v) [instb : ∀ a, Enumeration (β a)] : List (∀ a, β a) :=
  (List.pi insta.allValues fun x => (instb x).allValues).map (fun f x => f x (insta.complete x))

instance [insta : Enumeration α] [DecidableEq α] {β : α → Type v} [instb : ∀ a, Enumeration (β a)] : Enumeration (∀ a, β a) where
  allValues := (Enumeration.Pi.enum β)
  complete := by intro f ; simp [Enumeration.Pi.enum, List.mem_pi] ; exists (fun x _ => f x) ; simp ; grind

instance (l : List α) : Enumeration ({ a : α // a ∈ l }) where
  allValues := l.attach
  complete := by grind

instance [DecidableEq α] [Hashable α] (s : Std.HashSet α) : Enumeration ({ a : α // a ∈ s }) where
  allValues := s.toList.attachWith _ (by simp)
  complete := by grind

instance [DecidableEq α] [Hashable α] (s : Std.HashMap α β) : Enumeration ({ a : α // a ∈ s }) where
  allValues := s.keys.attachWith _ (by simp)
  complete := by simp

instance {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (s : Std.TreeSet α cmp) : Enumeration ({ a : α // a ∈ s }) where
  allValues := s.toList.attachWith _ (by simp)
  complete := by simp

instance {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (s : Std.TreeMap α β cmp) : Enumeration ({ a : α // a ∈ s }) where
  allValues := s.keys.attachWith _ (by simp)
  complete := by simp

instance {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (s : Std.ExtTreeSet α cmp) : Enumeration ({ a : α // a ∈ s }) where
  allValues := s.toList.attachWith _ (by simp)
  complete := by simp

instance {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (s : Std.ExtTreeMap α β cmp) : Enumeration ({ a : α // a ∈ s }) where
  allValues := s.keys.attachWith _ (by simp)
  complete := by simp

/-!
While some `Decidable` instances can be obtained by converting `Enumeration`
into `Fintype`, their efficiency is not clear.
-/

instance {α : Type u} [inst : Enumeration α] {p : α → Prop} [DecidablePred p] : Decidable (∀ a, p a) :=
  decidable_of_iff (∀ a ∈ inst.allValues, p a)
    (Iff.intro (fun h a => h _ (inst.complete a)) (fun h a _ => h a))

instance {α : Type u} [inst : Enumeration α] {p : α → Prop} [DecidablePred p] : Decidable (∃ a, p a) :=
  decidable_of_iff (∃ a ∈ inst.allValues, p a)
    (Iff.intro (fun ⟨a, _, h⟩ => ⟨a, h⟩) (fun ⟨a, h⟩ => ⟨a, inst.complete a, h⟩))

section EnumerationDerivingHandler

open Lean Meta Elab Term Command Deriving

private def mkAllValuesFromHeader (header : Header) (localInsts fieldNames : Array Name) : TermElabM Term := do
  -- for the types, knowing the length of `ts` should be enough
  let ts ← do
    let hole ← `(_)
    let holes := Array.replicate fieldNames.size hole
    `([$holes:term,*])
  let init ← `(([] : List $(header.targetType)))
  let f ← do
    let res ← mkIdent <$> mkFreshUserName `res
    let fieldIdents ← fieldNames.mapM (mkIdent <$> mkFreshUserName ·)
    `(fun $fieldIdents* $res => ⟨$fieldIdents,*⟩ :: $res)
  let enums ← do
    let arr ← localInsts.mapM fun inst => `(fun (_ : $(mkIdent ``Unit)) => $(mkIdent inst).$(mkIdent `allValues))
    let arr := arr.push (← `($(mkIdent ``Unit.unit)))
    `(⟨$arr,*⟩)
  `(@$(mkIdent ``IteratedProd.foldMap) _ $ts $init $f $enums)

def mkEnumerationInstCmdForStructure (declName : Name) : CommandElabM Bool := ForStructure.mkInstCmdTemplate declName fun info indVal header => do
  let fieldNames := info.fieldNames
  let (localInsts, binders') ← Array.unzip <$> mkInstImplicitBindersForFields ``Enumeration indVal header.argNames fieldNames
  let allValues ← mkAllValuesFromHeader header localInsts fieldNames
  let completeProof ← do
    let aIdent ← mkIdent <$> mkFreshUserName `a
    `(by intro $aIdent:ident ; cases $aIdent:ident ; simp [$(mkIdent ``IteratedProd.foldMap):ident] ; grind)
  `(instance $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
      $(mkIdent ``Enumeration) $(header.targetType) where
    $(mkIdent `allValues):ident := $allValues
    $(mkIdent `complete):ident  := $completeProof)

def mkEnumerationInstCmdGeneralCase (declName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct declName
  let cmd ← liftTermElabM do
    let instName ← mkInstName ``Enumeration declName
    let header ← mkHeader ``Enumeration 0 indVal
    let auxDefCmd ← do
      let funBinders ← header.binders.mapM bracketedBinderToFunBinder
      let target ← `(($(mkIdent ``Enumeration.ofEquiv) _ (proxy_equiv% $header.targetType) : $(mkIdent ``Enumeration) $header.targetType))
      let defBody ← mkFunSyntax funBinders target
      `(command|@[instance] def $(mkIdent instName) := remove_unused_args% $defBody)
    pure auxDefCmd
  elabVeilCommand cmd
  return true

def mkEnumerationInstCmd (declName : Name) : CommandElabM Bool := do
  if ← isEnumType declName then
    -- make use of `Fintype` deriving for enums, since it defines auxiliary definitions
    let ctorIdxName := declName.mkStr "ctorIdx"
    let enumListName := declName.mkStr "enumList"
    unless (← getEnv).contains enumListName do
      Mathlib.Deriving.Fintype.mkFintypeEnum declName
    let ctorThmName := declName.mkStr "enumList_getElem?_ctorIdx_eq"
    let x ← liftCoreM <| mkIdent <$> mkFreshUserName `x
    let cmd ← `(command|
      instance : $(mkIdent ``Enumeration) $(mkIdent declName) where
        $(mkIdent `allValues):ident := $(mkIdent enumListName)
        $(mkIdent `complete):ident := by
          intro $x:ident ; rw [$(mkIdent ``List.mem_iff_getElem?):ident]
          exact ⟨$(mkIdent ctorIdxName) $x, $(mkIdent ctorThmName) $x⟩)
    elabVeilCommand cmd
    return true
  orM (mkEnumerationInstCmdForStructure declName) (mkEnumerationInstCmdGeneralCase declName)

def mkEnumerationHandler := onlyHandleOne mkEnumerationInstCmd

initialize registerDerivingHandler ``Enumeration mkEnumerationHandler

end EnumerationDerivingHandler

end Enumeration

section FinEncodable

/-!
Sometimes we want to use the bijection between a finite type and `Fin n` for
some `n : Nat`, but the `FinEnum` instance generated by `FinEnum.ofList` might be
inefficient. Here we provide some (potentially) efficient instances for such types.
-/

/-- Essentially the same as `FinEnum`, but without `decEq`. -/
class FinEncodable (α : Type u) where
  card : Nat
  equiv : α ≃ Fin card

@[always_inline]
instance : FinEncodable Unit where
  card := 1
  equiv := { toFun := fun _ => ⟨0, by decide⟩
             invFun := fun _ => ()
             left_inv := fun _ => rfl
             right_inv := fun i => match i with | ⟨0, _⟩ => rfl }

@[always_inline]
instance : FinEncodable Empty where
  card := 0
  equiv := { toFun := Empty.elim
             invFun := Fin.elim0
             left_inv := fun e => Empty.elim e
             right_inv := fun i => Fin.elim0 i }

@[always_inline]
instance {n : Nat} : FinEncodable (Fin n) where
  card := n
  equiv := delta% Equiv.refl _

@[always_inline]
instance : FinEncodable Bool where
  card := 2
  equiv :=
    -- NOTE: Without providing proofs, Lean will insert unnecessary `Nat.mod` calls
    { toFun := fun b => bif b then ⟨1, by decide⟩ else ⟨0, by decide⟩
      invFun := fun i => i == ⟨1, by decide⟩
      left_inv := by grind
      right_inv := by grind }

@[inline]
def FinEncodable.encodeProd {α : Type u} {β : Type v} {n m : Nat}
  (fa : α → Fin n) (fb : β → Fin m) (p : α × β) : Fin (n * m) :=
  let (a, b) := p
  let i := fa a
  let j := fb b
  ⟨i.val * m + j.val, by
    calc i.val * m + j.val
      _ < i.val * m + m := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * m := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ n * m := Nat.mul_le_mul_right _ i.isLt⟩

@[inline]
def FinEncodable.decodeProd {α : Type u} {β : Type v} {n m : Nat}
  (fa : Fin n → α) (fb : Fin m → β) (k : Fin (n * m)) : α × β :=
  have hpos : 0 < m := Nat.pos_of_ne_zero (by
    intro h; simp only [h, Nat.mul_zero] at k; exact Fin.elim0 k)
  have hdiv : k.val / m < n := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    exact k.isLt
  let i : Fin n := ⟨k.val / m, hdiv⟩
  let j : Fin m := ⟨k.val % m, Nat.mod_lt _ hpos⟩
  (fa i, fb j)

theorem FinEncodable.decodeProd_encodeProd {α : Type u} {β : Type v} {n m : Nat}
  (equiva : α ≃ Fin n) (equivb : β ≃ Fin m) (p : α × β) :
  FinEncodable.decodeProd equiva.symm equivb.symm (FinEncodable.encodeProd equiva equivb p) = p := by
  rcases p with ⟨a, b⟩
  have hb := (equivb b).isLt
  have hpos : 0 < m := Nat.zero_lt_of_lt hb
  have heq1 : ((equiva a).val * m + (equivb b).val) / m =
      (equiva a).val := by
    conv_lhs => rw [Nat.add_comm, Nat.mul_comm]
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hb, Nat.zero_add]
  have heq2 : ((equiva a).val * m + (equivb b).val) % m =
      (equivb b).val := by
    conv_lhs => rw [Nat.add_comm, Nat.mul_comm]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  simp only [encodeProd, decodeProd, Prod.mk.injEq]
  constructor <;> rw [Equiv.symm_apply_eq] <;> ext <;> assumption

theorem FinEncodable.encodeProd_decodeProd {α : Type u} {β : Type v} {n m : Nat}
  (equiva : α ≃ Fin n) (equivb : β ≃ Fin m) (k : Fin (n * m)) :
  FinEncodable.encodeProd equiva equivb (FinEncodable.decodeProd equiva.symm equivb.symm k) = k := by
  simp only [encodeProd, decodeProd, Fin.ext_iff, Equiv.apply_symm_apply]
  apply Nat.div_add_mod'

@[inline]
instance [insta : FinEncodable α] [instb : FinEncodable β] : FinEncodable (α × β) where
  card := insta.card * instb.card
  equiv :=
    { toFun := fun p => FinEncodable.encodeProd insta.equiv instb.equiv p
      invFun := fun k => FinEncodable.decodeProd insta.equiv.symm instb.equiv.symm k
      left_inv := FinEncodable.decodeProd_encodeProd insta.equiv instb.equiv
      right_inv := FinEncodable.encodeProd_decodeProd insta.equiv instb.equiv }

@[inline]
instance [insta : FinEncodable α] [instb : FinEncodable β] : FinEncodable (α ⊕ β) where
  card := insta.card + instb.card
  equiv :=
    { toFun := fun
        | Sum.inl a => ⟨(insta.equiv a).val, by have := (insta.equiv a).isLt; omega⟩
        | Sum.inr b => ⟨insta.card + (instb.equiv b).val, by have := (instb.equiv b).isLt; omega⟩
      invFun := fun k =>
        if h : k.val < insta.card then
          Sum.inl (insta.equiv.symm ⟨k.val, h⟩)
        else
          Sum.inr (instb.equiv.symm ⟨k.val - insta.card, by have := k.isLt; omega⟩)
      left_inv := by
        intro x
        cases x
        · simp [(insta.equiv _).isLt]
        · simp [Nat.not_lt_of_le (Nat.le_add_right _ _)]
      right_inv := by
        intro k
        simp only [Fin.ext_iff]
        split_ifs with h <;> simp only [Equiv.apply_symm_apply]; omega }

@[inline]
instance [insta : FinEncodable α] : FinEncodable (Option α) where
  card := insta.card + 1
  equiv :=
    { toFun := fun
        | none => ⟨0, Nat.zero_lt_succ _⟩
        | some a => ⟨(insta.equiv a).val + 1, Nat.add_lt_add_right (insta.equiv a).isLt 1⟩
      invFun := fun k =>
        match k with
        | ⟨0, _⟩ => none
        | ⟨n + 1, h⟩ => some (insta.equiv.symm ⟨n, Nat.lt_of_succ_lt_succ h⟩)
      left_inv := by
        intro x
        cases x <;> simp [Equiv.symm_apply_apply]
      right_inv := by
        intro ⟨k, hk⟩
        cases k <;> simp [Equiv.apply_symm_apply] }

-- NOTE: after inlining, there seems to be no temporary pair allocation
@[inline]
def FinEncodable.encodeNonDepSigma {α : Type u} {β : Type v} {n m : Nat}
  (fa : α → Fin n) (fb : β → Fin m) (p : (_ : α) × β) : Fin (n * m) :=
  match p with
  | ⟨a, b⟩ => FinEncodable.encodeProd fa fb (a, b)

@[inline]
def FinEncodable.decodeNonDepSigma {α : Type u} {β : Type v} {n m : Nat}
  (fa : Fin n → α) (fb : Fin m → β) (k : Fin (n * m)) : (_ : α) × β :=
  let (a, b) := FinEncodable.decodeProd fa fb k
  ⟨a, b⟩

@[inline]
instance instFinEncodableNonDepSigma {α : Type u} {β : Type v} [insta : FinEncodable α] [instb : FinEncodable β] : FinEncodable ((_ : α) × β) where
  card := insta.card * instb.card
  equiv :=
    { toFun := fun p => FinEncodable.encodeNonDepSigma insta.equiv instb.equiv p
      invFun := fun k => FinEncodable.decodeNonDepSigma insta.equiv.symm instb.equiv.symm k
      left_inv := by
        have tmp := FinEncodable.decodeProd_encodeProd insta.equiv instb.equiv
        whnf ; simp [FinEncodable.encodeNonDepSigma, FinEncodable.decodeNonDepSigma]
        grind
      right_inv := by
        have tmp := FinEncodable.encodeProd_decodeProd insta.equiv instb.equiv
        whnf ; simp [FinEncodable.encodeNonDepSigma, FinEncodable.decodeNonDepSigma]
        grind }

theorem FinEncodable.card_ne_0_if_Inhabited [Inhabited α] [inst : FinEncodable α] : inst.card ≠ 0 :=
  if h : inst.card = 0 then
    let fin0 := h ▸ inst.equiv (default : α)
    Fin.elim0 fin0
  else
    Nat.ne_of_gt (Nat.pos_of_ne_zero h)

section FinEncodableDerivingHandler

open Lean Meta Elab Term Command Deriving

private theorem enumList_getElem?_ctorIdx_eq_implies_ctorIdx_lt {α : Type u} {l : List α}
  {f : α → Nat} (h : ∀ a : α, l[f a]? = some a) : ∀ a : α, f a < l.length := by grind

def mkFinEncodableInstCmd (declName : Name) : CommandElabM Bool := do
  if ← isEnumType declName then
    -- make use of `Fintype` deriving for enums, since it defines auxiliary definitions
    let ctorIdxName := declName.mkStr "ctorIdx"
    let enumListName := declName.mkStr "enumList"
    unless (← getEnv).contains enumListName do
      Mathlib.Deriving.Fintype.mkFintypeEnum declName
    let ctorThmName := declName.mkStr "enumList_getElem?_ctorIdx_eq"
    let x ← liftCoreM <| mkIdent <$> mkFreshUserName `x
    -- CHECK Will this proof result in huge proof object?
    let cmd ← `(command|
      instance : $(mkIdent ``FinEncodable) $(mkIdent declName) where
        $(mkIdent `card):ident := $(mkIdent ``List.length) $(mkIdent enumListName)
        $(mkIdent `equiv):ident :=
          { $(mkIdent `toFun):ident := fun $x:ident => ⟨$(mkIdent ctorIdxName) $x, $(mkIdent ``enumList_getElem?_ctorIdx_eq_implies_ctorIdx_lt) $(mkIdent ctorThmName) $x⟩
            $(mkIdent `invFun):ident := fun $x:ident => $(mkIdent enumListName)[$x]
            $(mkIdent `left_inv):ident := by
              whnf ; simp only [$(mkIdent ``Fin.getElem_fin):ident]
              intros ; rw [$(mkIdent ``List.getElem_eq_iff):ident] ; apply $(mkIdent ctorThmName)
            $(mkIdent `right_inv):ident := by
              whnf ; simp only [$(mkIdent ``Fin.getElem_fin):ident] ; unfold $(mkIdent enumListName) ; dsimp ; decide
          })
    elabVeilCommand cmd
    return true
  -- orM (mkFinEncodableInstCmdForStructure declName) (mkFinEncodableInstCmdGeneralCase declName)
  return false

def mkFinEncodableHandler := onlyHandleOne mkFinEncodableInstCmd

initialize registerDerivingHandler ``FinEncodable mkFinEncodableHandler

end FinEncodableDerivingHandler

end FinEncodable

section OptionalTypeclassInstance

/-- For optionally holding a typeclass instance. This can be used where
a typeclass instance may or may not exist. -/
class OptionalTC (tc : Type u) where
  body : Option tc

abbrev OptionalEnumeration := OptionalTC ∘ Enumeration
abbrev OptionalFinEncodable := OptionalTC ∘ FinEncodable

set_option checkBinderAnnotations false in
instance (priority := high) instOptionalTCSome [inst : tc] : OptionalTC tc where
  body := Option.some inst

set_option checkBinderAnnotations false in
instance (priority := low) instOptionalTCNone : OptionalTC tc where
  body := Option.none

namespace OptionalTC

open Lean Elab Command Meta Term

/-- Given `df : ... → (f : T) → IteratedProd ((xs f).map (fun x => OptionalTC (tc x)))`
where `T` is an enum type, this generates an array of `Bool` such that
for each constructor `c : T`, the corresponding `Bool` indicates whether
all `OptionalTC` instances are `some` when applying `df` to `c`. -/
private def genAllSomePredicateCore (dfName : Name) : MetaM (Name × Array Bool) := do
  let dfName ← resolveGlobalConstNoOverloadCore dfName
  let dfInfo ← getConstInfo dfName
  let some dfExpr := dfInfo.value?
    | throwError "{dfName} is not a definition"
  let (labelType, argsSize) ← do
    forallTelescope dfInfo.type fun args _ => do
      let l := args.back!
      let ty ← inferType l
      pure (ty, args.size)
  let some labelTypeName := labelType.constName?
    | throwError "Could not determine label type from definition {dfName}"
  unless ← isEnumType labelTypeName do
    throwError "Label type {labelTypeName} is not an enum type"
  let .inductInfo indVal ← getConstInfo labelTypeName
    | throwError "Could not retrieve inductive info for {labelTypeName}"
  let results ← do
    indVal.ctors.mapM fun ctor => do
      lambdaBoundedTelescope dfExpr (argsSize - 1) fun _ body => do
        -- Exploit the fact that label types don't have universe parameters
        let ctorExpr := Lean.mkConst ctor
        let app := mkApp body ctorExpr
        let result ← whnf app
        pure <| Bool.not <| hasNoneInstance result
  pure (labelTypeName, results.toArray)
where hasNoneInstance (e : Expr) : Bool :=
  Option.isSome <| e.find? fun subExpr => subExpr.isConstOf ``instOptionalTCNone

def genAllSomePredicateSyntax (dfName : Name) : MetaM (TSyntax ``Parser.Term.bracketedBinder × Term) := do
  let (labelTypeName, results) ← genAllSomePredicateCore dfName
  let casesOn := labelTypeName ++ `casesOn
  let quotedResults : Array Term := results.map quote
  let l ← Lean.mkIdent <$> mkFreshBinderName
  let binder ← `(bracketedBinder| ($l : $(mkIdent labelTypeName)))
  let body ← `($(mkIdent casesOn) $l $quotedResults*)
  pure (binder, body)

def genAllSomePredicateTermElab (dfName : Name) : TermElabM Expr := do
  let (labelTypeName, results) ← genAllSomePredicateCore dfName
  let casesOn := labelTypeName ++ `casesOn
  let l ← mkFreshUserName `l
  withLocalDeclD l (mkConst labelTypeName) fun lIdent => do
    let motive ← mkLambdaFVars #[lIdent] (mkConst ``Bool)
    let body ← mkAppOptM casesOn (#[motive, lIdent] ++ results.map (toExpr ·) |>.map Option.some)
    mkLambdaFVars #[lIdent] body

-- def genAllSomePredicateDefSyntax (dfName : Name) (outputName : Name) : MetaM Command := do
--   let (binder, body) ← genAllSomePredicateSyntax dfName
--   `(def $(mkIdent outputName) $binder:bracketedBinder : $(mkIdent ``Bool) := $body:term)

-- def genAllSomePredicateCmd (dfName : Name) (outputName : Name) : CommandElabM Unit := do
--   let cmd ← liftTermElabM <| genAllSomePredicateDefSyntax dfName outputName
--   elabVeilCommand cmd

def genAllSomePredicateCmd [Monad m] [MonadQuotation m] [MonadError m] (dfName : Name) (outputName : Name) : m Syntax := do
  let checkTerm := Syntax.mkApp (mkIdent ``OptionalTC.genAllSomePredicateTermElab) #[quote dfName]
  `(def $(mkIdent outputName) := by_elab $checkTerm:term)

end OptionalTC

end OptionalTypeclassInstance

end Veil
