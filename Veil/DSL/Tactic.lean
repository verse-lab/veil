import Lean.Elab.Tactic
import Veil.DSL.Util
import Veil.SMT.Main

open Lean Lean.Elab

/--
  `exact_state` is usually used after `funcases` ar `funcasesM`. At this point the goal should
  contain all state fields as hypotheses. This tactic will then construct the
  state term using the field hypotheses and close the goal.
-/
elab "exact_state" : tactic => do
  let stateName ← getStateName
  let stateTp := (<- localSpecCtx.get).spec.stateType
  let .some sn := stateTp.constName?
    | throwError "{stateTp} is not a constant"
  let .some _sinfo := getStructureInfo? (<- getEnv) sn
    | throwError "{stateTp} is not a structure"
  let fns := _sinfo.fieldNames.map mkIdent
  -- fileds' names should be the same as ones in the local context
  let constr <- `(term| (⟨$[$fns],*⟩ : $(mkIdent stateName) ..))
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
    trace[dsl.debug] "[conv!] {e}\nsimplifies to\n{e'}"
  )
  return rhs

/-- We use this to evaluate `wlp` inside function bodies at definition time.
  Otherwise it has to be evaluated in the kernel during proofs, which is very slow.
  `conv!` applies a tactic to a term. -/
def unfoldWlp (t : TSyntax `term) : TermElabM (TSyntax `term) := do
  let actSimp := mkIdent `actSimp
  -- We have to do this round-about `let t : = .. ; exact t` because we
  -- want to delay the evaluation of `t` until types are available to be
  -- inferred, otherwise `$t` might fail to type-check.
  let t' ← `(term|by first | let t := conv! (dsimp only [$actSimp:ident]) => $t; exact t | exact $t)
  return t'

/-- This does `unfoldWlp` followed by some other simplifications. -/
def simplifyTerm (t : TSyntax `term) : TermElabM (TSyntax `term) := do
  let (actSimp, smtSimp, logicSimp, elim_exists_State) := (mkIdent `actSimp, mkIdent `smtSimp, mkIdent `logicSimp, mkIdent ``elim_exists_State)
  -- Reduce the body of the function
  let t' ← `(term| by
    first | (let t := conv! (dsimp only [$actSimp:ident]; simp only [$smtSimp:ident, $logicSimp:ident]; simp only [and_assoc]; simp only [↓ $elim_exists_State:ident]) => $t; exact t) | exact $t)
  return t'
