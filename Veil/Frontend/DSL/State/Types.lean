import Mathlib.Logic.Equiv.Defs

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

end IteratedProd

end Veil
