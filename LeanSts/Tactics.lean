import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import LeanSts.TransitionSystem
import LeanSts.DSLUtil

-- For automation
import Auto
import Duper

-- Register our own version of @[simp], i.e. @[sts]
-- We add this to (hopefully) improve the performance of `simp`
-- by not looking through all the mathlib lemmas.
register_simp_attr sts

open Lean Lean.Elab.Tactic

-- Creates a fresh variable with the suggested name.
def fresh [Monad m] [Lean.MonadLCtx m] (suggestion : Lean.Name) : m Lean.Syntax.Ident := do
  let name ← Meta.getUnusedUserName suggestion
  return Lean.mkIdent name

def isPrimed (n : Name) : Bool := n.getString!.endsWith "'"
def getNumPrimes (n : Name) : Nat := n.getString!.foldl (fun n c => if c == '\'' then n + 1 else n) 0

/-- Destruct a structure into its fields.
    If no identifier is provided, destructs the goal. -/
elab "sdestruct " ids:(colGt ident)* : tactic => withMainContext do
  if ids.size == 0 then
    evalTactic $ ← `(tactic| repeat' constructor)
  else for id in ids do
    let lctx ← Lean.MonadLCtx.getLCtx
    let name := (getNameOfIdent' id)
    let .some ld := lctx.findFromUserName? name
      | throwError "sdestruct: {id} is not in the local context"
    let .some sn := ld.type.getAppFn.constName?
      | throwError "sdestruct: {id} is not a constant"
    let .some _sinfo := getStructureInfo? (<- getEnv) sn
      | throwError "sdestruct: {id} ({sn} is not a structure)"
    let newFieldNames := _sinfo.fieldNames.map (mkIdent $ name ++ ·)
    let s <- `(rcasesPat| ⟨ $[$newFieldNames],* ⟩)
    evalTactic $ ← `(tactic| unhygienic rcases $(mkIdent ld.userName):ident with $s)

elab "sintro " ids:(colGt ident)* : tactic => withMainContext do
  evalTactic $ ← `(tactic| intro $(ids)* ; sdestruct $(ids)*)

elab "sts_induction" : tactic => withMainContext do
  let lctx ← Lean.MonadLCtx.getLCtx
  -- (1) Identify the `next` hypothesis
  let opt_hnext ← lctx.findDeclM? fun (ldecl : Lean.LocalDecl) => do
    let declExpr := ldecl.toExpr
    let declType ← Meta.inferType declExpr
    if declType.isAppOf `RelationalTransitionSystem.next then
      return some ldecl
    else
      return none
  let hnext ← match opt_hnext with
  | none => throwError "sts_induction tactic failed: no `next` hypothesis found"
  | some hnext => pure hnext
  let hnextName := mkIdent hnext.userName
  let htrName ← fresh "htr"
  evalTactic  $ ← `(tactic| revert $hnextName; intro $htrName:ident)
  let case_split ← `(tactic| repeat' (rcases $htrName:ident with $htrName | $htrName))
  -- (2) Destruct the `next` hypothesis into separate goals for each individual action
  evalTactic $ case_split
  return

/--
  `exact_state` is usually used after `funcases`. At this point the goal should
  contain all state fields as hypotheses. This tactic will then construct the
  state term using the field hypotheses and close the goal.
-/
elab "exact_state" : tactic => do
  let stateTp := (<- stsExt.get).typ
  let .some sn := stateTp.constName?
    | throwError "{stateTp} is not a constant"
  let .some _sinfo := getStructureInfo? (<- getEnv) sn
    | throwError "{stateTp} is not a structure"
  let fns := _sinfo.fieldNames.map mkIdent
  -- fileds' names should be the same as ones in the local context
  let constr <- `(term| (⟨$[$fns],*⟩ : $(mkIdent "State") ..))
  evalTactic $ ← `(tactic| exact $constr)
