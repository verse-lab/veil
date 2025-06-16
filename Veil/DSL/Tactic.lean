import Lean.Elab.Tactic
import Veil.Util.DSL
import Veil.SMT.Main
import Veil.Theory.WP
import Veil.DSL.Action.Lang -- TODO: can we remove this?

open Lean Lean.Elab

/--
  `exact_state` is usually used after `funcases` ar `funcasesM`. At this point the goal should
  contain all state fields as hypotheses. This tactic will then construct the
  state term using the field hypotheses and close the goal.
-/
elab "exact_state" : tactic => do
  let stateTp := (<- localSpecCtx.get).spec.generic.stateType
  let .some sn := stateTp.constName?
    | throwError "{stateTp} is not a constant"
  let .some _sinfo := getStructureInfo? (<- getEnv) sn
    | throwError "{stateTp} is not a structure"
  let fns := _sinfo.fieldNames.map mkIdent
  -- fileds' names should be the same as ones in the local context
  let constr <- `(term| (⟨$[$fns],*⟩ : $(← getStateTpStx)))
  Tactic.evalTactic $ ← `(tactic| exact $constr)

/--
  `exact_reader` is usually used after `funcases` ar `funcasesM`. At this point the goal should
  contain all reader fields as hypotheses. This tactic will then construct the
  reader term using the field hypotheses and close the goal.
-/
elab "exact_reader" : tactic => do
  let readerTp := (<- localSpecCtx.get).spec.generic.readerType
  let .some sn := readerTp.constName?
    | throwError "{readerTp} is not a constant"
  let .some _sinfo := getStructureInfo? (<- getEnv) sn
    | throwError "{readerTp} is not a structure"
  let fns := _sinfo.fieldNames.map mkIdent
  -- fileds' names should be the same as ones in the local context
  let constr <- `(term| (⟨$[$fns],*⟩ : $(← getReaderTpStx)))
  Tactic.evalTactic $ ← `(tactic| exact $constr)

open Tactic in
elab _tk:"conv! " conv:conv " => " e:term : term => do
  let e ← Elab.Term.elabTermAndSynthesize e none
  let (rhs, g) ← Conv.mkConvGoalFor e
  _ ← Tactic.run g.mvarId! (do
    evalTactic conv
    for mvarId in (← getGoals) do
      liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
    pruneSolvedGoals
    let e' ← instantiateMVars rhs
    trace[veil.debug] "[conv!] {e}\nsimplifies to\n{e'}"
  )
  return rhs

/-
/-- We use this to evaluate `wp` inside function bodies at definition time.
  Otherwise it has to be evaluated in the kernel during proofs, which is very slow.
  `conv!` applies a tactic to a term. -/
def unfoldWp (t : TSyntax `term) : TermElabM (TSyntax `term) := do
  let actSimp := mkIdent `actSimp
  -- We have to do this round-about `let t : = .. ; exact t` because we
  -- want to delay the evaluation of `t` until types are available to be
  -- inferred, otherwise `$t` might fail to type-check.
  let t' ← `(term|by first | let t := conv! (dsimp only [$actSimp:ident]; unfold_wp; dsimp only) => $t; exact t | exact $t)
  return t'

def dsimpOnly (t : TSyntax `term) (classes : Array Name := #[]) : TermElabM (TSyntax `term) := do
  let classes := classes.map mkIdent
  let t' ← `(term|by first | let t := conv! (dsimp only [$[$classes:ident],*]) => $t; exact t | exact $t)
  return t'

/-- This does `unfoldWp` followed by some other simplifications. -/
def simplifyTerm (t : TSyntax `term) : TermElabM (TSyntax `term) := do
  let (actSimp, smtSimp, logicSimp, wpSimp, quantifierSimp) := (mkIdent `actSimp, mkIdent `smtSimp, mkIdent `logicSimp, mkIdent `wpSimp, mkIdent `quantifierSimp)
  -- Reduce the body of the function
  let t' ← `(term| by
    -- Try simplifying first, but this might fail if there's no `wp` in the
    -- definition, e.g. for transitions that are not actions.
    -- If that fails, we try to evaluate the term as is.
    -- We do `simp only [and_assoc]` at the end to normalize conjunctions.
    first | (let t := conv! (
        dsimp only [$actSimp:ident];
        -- for two-state version of the cation
        unfold_wp
        simp only [$wpSimp:ident, $smtSimp:ident, $logicSimp:ident];
        simp only [$quantifierSimp:ident]) => $t; exact t) | exact $t)
  return t'
-/
