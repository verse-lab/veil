module

/-
The introv elaborator is adapted from Mathlib.Tactic.Basic (Apache 2.0).
Copyright (c) 2018 Gabriel Ebner.
-/
public meta import Veil.Util.Equiv
public meta import Veil.Util.SetTactic
public meta import Veil.Util.SplitIfs

public meta section
namespace Veil.Tactic
open Lean Elab Tactic Meta
syntax (name := introv) "introv" (ppSpace colGt binderIdent)* : tactic
@[tactic introv] partial def evalIntrov : Tactic := fun stx ↦ do
  match stx with
  | `(tactic| introv)                     => introsDep
  | `(tactic| introv $h:ident $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro $h:ident; introv $hs:binderIdent*))
  | `(tactic| introv _%$tk $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro _%$tk; introv $hs:binderIdent*))
  | _ => throwUnsupportedSyntax
where
  introsDep : TacticM Unit := do
    let t ← getMainTarget
    match t with
    | Expr.forallE _ _ e _ =>
      if e.hasLooseBVars then
        intro1PStep
        introsDep
    | _ => pure ()
  intro1PStep : TacticM Unit :=
    liftMetaTactic fun goal ↦ do
      let (_, goal) ← goal.intro1P
      pure [goal]


end Veil.Tactic

namespace Veil.Tactic
open Lean Elab Tactic Meta
elab "whnf" : tactic => liftMetaTactic fun g => do
  pure [← g.replaceTargetDefEq (← Meta.whnf (← g.getType))]
elab "whnf" " at " hs:ident+ : tactic => do
  for h in hs do
    withMainContext do
      let f ← getFVarId h
      let t ← Meta.whnf (← f.getType)
      liftMetaTactic fun g => return [← g.changeLocalDecl f t]
end Veil.Tactic
