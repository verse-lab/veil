import Veil

open Lean Elab Command

private def hasForallBinderNamed (target : Name) (e : Expr) : Bool :=
  (e.find? fun
    | .forallE n _ _ _ => n == target
    | _ => false).isSome

private def hasLetBinderNamed (target : Name) (e : Expr) : Bool :=
  (e.find? fun
    | .letE n _ _ _ _ => n == target
    | _ => false).isSome

private def containsConst (target : Name) (e : Expr) : Bool :=
  (e.find? fun
    | .const n _ => n == target
    | _ => false).isSome

private partial def countConst (target : Name) : Expr → Nat
  | .const n _ => if n == target then 1 else 0
  | .app f a => countConst target f + countConst target a
  | .lam _ t b _ => countConst target t + countConst target b
  | .forallE _ t b _ => countConst target t + countConst target b
  | .letE _ t v b _ => countConst target t + countConst target v + countConst target b
  | .mdata _ b => countConst target b
  | .proj _ _ b => countConst target b
  | _ => 0

private def constValue (constName : Ident) : CommandElabM Expr := do
  let constName ← resolveGlobalConstNoOverload constName
  let info ← getConstInfo constName
  let some value := info.value?
    | throwError "{constName} does not have a value"
  pure value

elab "#guard_const_has_forall_binder " constName:ident binderName:ident : command => do
  let value ← constValue constName
  unless hasForallBinderNamed binderName.getId value do
    throwError "{constName} does not contain a forall binder named {binderName.getId}"

elab "#guard_const_has_let_binder " constName:ident binderName:ident : command => do
  let value ← constValue constName
  unless hasLetBinderNamed binderName.getId value do
    throwError "{constName} does not contain a let binder named {binderName.getId}"

elab "#guard_const_contains " constName:ident targetName:ident : command => do
  let value ← constValue constName
  let targetName ← resolveGlobalConstNoOverload targetName
  unless containsConst targetName value do
    throwError "{constName} does not contain constant {targetName}"

elab "#guard_const_not_contains " constName:ident targetName:ident : command => do
  let value ← constValue constName
  let targetName ← resolveGlobalConstNoOverload targetName
  if containsConst targetName value then
    throwError "{constName} still contains constant {targetName}"

elab "#guard_const_occurs_exactly " constName:ident targetName:ident n:num : command => do
  let value ← constValue constName
  let targetName ← resolveGlobalConstNoOverload targetName
  let actual := countConst targetName value
  let expected := n.getNat
  unless actual == expected do
    throwError "{constName} contains constant {targetName} {actual} times, expected {expected}"

veil module LetEqWP

type node
relation r : node → node → Bool

#gen_state

ghost relation g (a : node) :=
  r a a ∨ r a (if r a a then a else a) ∨ r (if r a a then a else a) a

action step (a : node) (b : node) (c : node) {
  veil_let dd := if r a b then a else c
  -- If the hidden expression will be used in executable control flow, hide a
  -- `Bool`, not a `Prop`: `veil_let ee : Prop := ...; if ... ¬ ee then ...`
  -- would leave Lean trying to synthesize `Decidable ee` for an abstract
  -- proposition. Put the decision on the right-hand side instead.
  veil_let ee : Bool := decide (veil_let (ga, gb) := (g a, g b);
    (ga ∨ gb ∨ g c) ∧ (¬ ga ∨ ¬ gb ∨ ¬ g c) ∧ (¬ ga ∨ gb ∨ g c)
  )
  if dd = a ∧ ee = false then
    r a b := true
  else
    if dd = c ∧ ee = false then
      r c a := true
}

action patternAndThis (a : node) (b : node) {
  veil_let pair := (a, b)
  veil_let (left, right) := pair
  veil_let : Bool := r left right
  if this then
    r right left := true
}

end LetEqWP

#print LetEqWP.step.ext.wp

#guard_const_has_forall_binder LetEqWP.step.ext.wp dd
#guard_const_has_forall_binder LetEqWP.step.ext.wp ee
#guard_const_contains LetEqWP.step.ext.wp Veil.letEq
#guard_const_occurs_exactly LetEqWP.step.ext.wp LetEqWP.g 5
#guard_const_has_forall_binder LetEqWP.patternAndThis.ext.wp pair
#guard_const_has_forall_binder LetEqWP.patternAndThis.ext.wp this

veil module LetEqBoolControl

individual flag : Bool

after_init {
  flag := false
}

action setFlag {
  -- This is the executable-control-flow pattern: hide a decided `Bool`, then
  -- branch on that Bool.
  veil_let enabled : Bool := decide (flag = false ∨ flag = true)
  if enabled then
    flag := true
  else
    flag := false
}

invariant true

#gen_spec

#model_check interpreted {  }

end LetEqBoolControl

veil module LetEqExtraction

individual flag : Bool

after_init {
  flag := false
}

action setFlag {
  veil_let next := true
  flag := next
}

invariant true

#gen_spec

#model_check interpreted {  }

end LetEqExtraction

#print LetEqExtraction.NextAct.extracted

-- #guard_const_not_contains LetEqExtraction.NextAct.extracted Veil.letEq
-- #guard_const_not_contains LetEqExtraction.NextAct.extracted Veil.eqWithoutSubst
