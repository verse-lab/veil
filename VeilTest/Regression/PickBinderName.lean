import Veil

open Lean Elab Command

private def hasForallBinderNamed (target : Name) (e : Expr) : Bool :=
  (e.find? fun
    | .forallE n _ _ _ => n == target
    | _ => false).isSome

elab "#guard_const_has_forall_binder " constName:ident binderName:ident : command => do
  let constName ← resolveGlobalConstNoOverload constName
  let info ← getConstInfo constName
  let some value := info.value?
    | throwError "{constName} does not have a value"
  unless hasForallBinderNamed binderName.getId value do
    throwError "{constName} does not contain a forall binder named {binderName.getId}"

veil module PickBinderName

type node

relation marker : node → Bool

#gen_state

ghost relation isfoobarino (n : node) (foobarino : node) :=
  n = foobarino

action pickAction (n : node) {
  let foobarino ← pick node
  require isfoobarino n foobarino
}

action pickSuchThatAction (n : node) {
  let foobarino : node :| isfoobarino n foobarino
  require True
}

end PickBinderName

#guard_const_has_forall_binder PickBinderName.pickAction.ext.wp foobarino

#guard_const_has_forall_binder PickBinderName.pickSuchThatAction.ext.wp foobarino
