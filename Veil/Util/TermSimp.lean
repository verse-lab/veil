import Lean

/-
  This file provides facilities for running tactics on terms. In
  particular, it provides a version of `Tactic.run` that returns a
  value. This is used to provide the `runSimp` method for Lean `Expr`s
  that runs within `TermElabM` rather than `TacticM`.
-/

theorem foo (p : Prop) [dec : Decidable p] (dec' : Decidable p) : dec' = dec := by
  sorry

theorem decidable_irrelevance (p : Prop) (i1 i2 : Decidable p) : i1 = i2 := by
  cases i1 <;> cases i2 <;> sorry

theorem ite_decidable_irrelevance c (e1 e2 : α) (i1 i2 : Decidable c) :
  @ite _ c i1 e1 e2 = @ite _ c i2 e1 e2 := by congr


#check Lean.Expr.rep

open Lean Meta Elab Term in
simproc ↓ replaceDecidableInst (_) := fun e => do
  let args := e.getAppArgs
  let mut agrsNew := #[]
  for arg in args do
    match_expr  arg.consumeMData with
    | Classical.propDecidable p =>
      let q ← synthInstance (mkApp (mkConst ``Decidable) p)
      -- let proof := mkAppN (mkConst ``decidable_irrelevance) #[p, arg, q]
      agrsNew := agrsNew.push q
    | _ =>
      agrsNew := agrsNew.push arg
  return .done { expr := mkAppN e.getAppFn agrsNew, proof? := none }

#check Classical.propDecidable


#check Lean.Expr.replace

set_option pp.all true
example (n : Nat) (P : (n : Nat) -> [Decidable (n = n)] -> Prop) : @P n (Classical.propDecidable _) := by
  simp only [replaceDecidableInst]

variable {node : Type} [node_dec : DecidableEq node] [node_ne : Nonempty node]

def tot.le (a b : node) : Prop := sorry

open Classical in
noncomputable
def qb (a b : node) : Bool := if tot.le a b then true else false

variable [DecidableRel tot.le]

example (a b : node) (P : _ -> Prop) : P (qb a b) := by
  unfold qb
  simp only [replaceDecidableInst]

namespace Tactic
open Lean Elab Command Tactic

abbrev Context := Lean.Elab.Tactic.Context
abbrev State := Lean.Elab.Tactic.State

@[inline] private def _runCore (x : TacticM α) (ctx : Context) (s : State) : TermElabM (α × State) :=
  x ctx |>.run s

@[inline] private def _runCore' (x : TacticM α) (ctx : Context) (s : State) : TermElabM α :=
  Prod.fst <$> _runCore x ctx s

/-- This is a copy of `Tactic.run` that returns a value. -/
def run  (mvarId : MVarId) (x : TacticM α) : TermElabM (α × List MVarId) :=
  mvarId.withContext do
   let pendingMVarsSaved := (← get).pendingMVars
   modify fun s => { s with pendingMVars := [] }
   let aux : TacticM (α × List MVarId) :=
     try
       let ret ← x
       let unsolved ← getUnsolvedGoals
       return (ret, unsolved)
     catch ex =>
         throw ex
   try
     _runCore' aux { elaborator := .anonymous } { goals := [mvarId] }
   finally
     modify fun s => { s with pendingMVars := pendingMVarsSaved }
end Tactic

def veilSimpMaxSteps := 10 * Lean.Meta.Simp.defaultMaxSteps

open Lean.Elab Tactic Lean.Meta
def Lean.Expr.runSimp (e : Expr) (stx : TermElabM (TSyntax `tactic)) : TermElabM Simp.Result := do
  let stx ← stx
  let mv := (← mkFreshExprMVar e)
  let (res, [_l]) ← Tactic.run mv.mvarId! (do
    let sc <- mkSimpContext stx false
    let cfg := { sc.ctx.config with maxSteps := veilSimpMaxSteps }
    let ctx ← sc.ctx.setConfig cfg
    let res <- simp e ctx (simprocs := sc.simprocs) (discharge? := none)
    return res
  ) | throwError "[runSimp] expected exactly one goal after simplification"
  return res.1

def Lean.Expr.simp (e : Expr) (act : Array Name) : TermElabM Simp.Result := do
  let act := act.map mkIdent
  let stx :=
   `(tactic| simp only [$[$act:ident],*])
  e.runSimp stx


def Lean.Expr.simpWp (e : Expr) (act : Name) : TermElabM Simp.Result := do
  let stx :=
   `(tactic| simp only [wpSimp, $(mkIdent act):ident, smtSimp, quantifierSimp])
  e.runSimp stx

def Lean.Expr.simpWpSucc (e : Expr) (act : Name) : TermElabM Simp.Result := do
  let stx :=
   `(tactic| simp only [$(mkIdent act):ident, if_true_right])
  e.runSimp stx

def Lean.Expr.simpWpEx (e : Expr) (act : Name) : TermElabM Simp.Result := do
  let stx :=
   `(tactic| simp only [$(mkIdent act):ident])
  e.runSimp stx

def Lean.Expr.simpAction (e : Expr) : TermElabM Simp.Result := do
  let stx := `(tactic| simp only [$(mkIdent `VeilM.require):ident, $(mkIdent `VeilM.ensure):ident])
  e.runSimp stx

def Lean.Expr.runUnfold (e : Expr) (defs : List Name) : TermElabM Expr := do
  let mut eu := e
  for name in defs do eu := (<- unfold eu name).expr
  return eu
