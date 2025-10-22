import Lean


namespace Veil

/-
  This file provides facilities for running tactics on terms. In
  particular, it provides a version of `Tactic.run` that returns a
  value. This is used to provide the `runSimp` method for Lean `Expr`s
  that runs within `TermElabM` rather than `TacticM`.
-/

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

open Lean Lean.Elab Tactic Lean.Meta
def runSimp (e : Expr) (stx : TermElabM (TSyntax `tactic)) : TermElabM Simp.Result := do
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

def simpWp (e : Expr) : TermElabM Simp.Result := do
  let stx := `(tactic| simp only [wpSimp])
  runSimp e stx

def simpAction (e : Expr) : TermElabM Simp.Result := do
  let stx := `(tactic| simp only [actSimp, smtSimp, quantifierSimp])
  runSimp e stx

def runUnfold (e : Expr) (defs : List Name) : TermElabM Expr := do
  let mut eu := e
  for name in defs do eu := (<- unfold eu name).expr
  return eu

end Veil
