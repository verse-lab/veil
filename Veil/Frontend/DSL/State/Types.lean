import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.FinEnum
import Veil.Frontend.DSL.Module.Names
import Veil.Util.Deriving
import Mathlib.Tactic.DeriveFintype

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
  [decEq : DecidableEq α]

def Enumeration.ofEquiv (α : Type u) {β : Type v} [inst : Enumeration α] [dec : DecidableEq β] (h : α ≃ β) : Enumeration β where
  allValues := inst.allValues.map h
  complete := by simp ; intro b ; exists (h.symm b) ; simp ; apply inst.complete
  decEq := dec

attribute [instance low] Enumeration.decEq
attribute [grind ←] Enumeration.complete

instance (priority := high) [enum : Enumeration α] : FinEnum α := FinEnum.ofList enum.allValues enum.complete
/-!
Here only gives some basic instances. More complicated ones should be
found in `Veil.Frontend.Std`.
-/

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

def Enumeration.Pi.enum [insta : Enumeration α] (β : α → Type v) [instb : ∀ a, Enumeration (β a)] : List (∀ a, β a) :=
  (List.pi insta.allValues fun x => (instb x).allValues).map (fun f x => f x (insta.complete x))

instance [insta : Enumeration α] {β : α → Type v} [instb : ∀ a, Enumeration (β a)] : Enumeration (∀ a, β a) where
  allValues := (Enumeration.Pi.enum β)
  complete := by intro f ; simp [Enumeration.Pi.enum, List.mem_pi] ; exists (fun x _ => f x) ; simp ; grind

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
    let header ← mkHeader ``Enumeration 0 indVal
    let binders' ← mkInstImplicitBinders `Decidable indVal header.argNames
    `(command|
      instance $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
        $(mkIdent ``Enumeration) $header.targetType :=
      $(mkIdent ``Enumeration.ofEquiv) _ (proxy_equiv% $header.targetType))
  elabVeilCommand cmd
  return true

def mkEnumerationInstCmd (declName : Name) : CommandElabM Bool := do
  if ← isEnumType declName then
    -- make use of `Fintype` deriving for enums, since it defines auxiliary definitions
    Mathlib.Deriving.Fintype.mkFintypeEnum declName
    let ctorIdxName := declName.mkStr "ctorIdx"
    let enumListName := declName.mkStr "enumList"
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

end Veil
