import Smt
import Lean
import Veil.SMT.Main
import Veil.DSL.TacticUtil
import Veil.Tactic.Main
import Auto.Solver.SMT
import Auto

open Lean hiding Command Declaration

open Lean Elab Command Term Meta Tactic in
/-- This performs the same simplifications as `fast_simplify_clause` on
the given expression and then passes it to the SMT translator.-/
def translateExprToSmt (expr: Expr) : TermElabM String := do
  let g ← mkFreshExprMVar expr
  let [l] ← Tactic.run g.mvarId! (do
    tryGoal $ run `(tactic|unhygienic intros; fast_simplify_clause)
    for mvarId in (← Tactic.getGoals) do
      liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
    Tactic.pruneSolvedGoals
    -- Reverts everything that is not `Type`
    withMainContext do
      let hypsNew <- getLCtx
      for hyp in hypsNew.decls.toArray.reverse do
        if hyp.isSome then
          let hyp := hyp.get!
          unless hyp.type.isType do
            tryGoal $ run `(tactic| revert $(mkIdent hyp.userName):ident)
   ) | throwError "[translateExprToSmt] expected exactly one goal after simplification"
  let cmd ← forallTelescope (<- l.getType)
    fun ks tp => do
    let props ← ks.filterM (fun k => return ← Meta.isProp (← inferType k))
    let (fvNames₁, _) ← Smt.genUniqueFVarNames
    let cmds ← Smt.prepareSmtQuery props.toList tp fvNames₁
    let cmdString := s!"{Smt.Translate.Command.cmdsAsQuery cmds}"
    pure cmdString
  return cmd

open Smt Smt.Tactic Translate Lean Lean.Meta Auto.Solver.SMT in
def querySolverWithIndicators (goalQuery : String) (timeout : Nat) (checks: Array (Array (Name × Expr))) (forceSolver : Option SolverName := none)
  : MetaM (List ((List Name) × SmtResult)) := do
  withTraceNode `sauto.perf.query (fun _ => return "querySolverWithIndicators") do
  let opts ← getOptions
    let solverName :=
      match forceSolver with
      | some s => s
      | none => sauto.smt.solver.get opts
    trace[sauto.debug] "solver: {solverName}"
  try
    let solver ← createSolver solverName timeout
    if solverName == SolverName.cvc5 then
      emitCommand solver (.setLogic "ALL")
      emitCommand solver (.setOption (.produceProofs true))
      emitCommand solver (.setOption (.produceUnsatCores true))
    emitCommandStr solver s!"{goalQuery}\n"
    let mut ret := []

    let indicatorNames := (checks.map (fun arr => arr.map (fun (_, ind) => ind.constName!))).flatten

    for check in checks do
      trace[sauto.debug] "Now running solver"
      let variablesInCheck := (check.map (fun (act, _) => act)).toList
      let indicatorsInCheck := check.map (fun (_, ind) => ind.constName!)
      let expression := indicatorNames.foldl (fun acc new =>
        if indicatorsInCheck.contains new then
          s!"{mkPrintableName new} {acc}"
        else s!"(not {mkPrintableName new}) {acc}") ""
      emitCommandStr solver s!"(check-sat-assuming (and {expression}))\n"
      let stdout ← Handle.readLineSkip solver.stdout
      let (checkSatResponse, _) ← getSexp stdout
      let checkSatResponse: SmtResult := match checkSatResponse with
        | .atom (.symb "sat") => SmtResult.Sat none
        | .atom (.symb "unsat") => SmtResult.Unsat (.app #[])
        | e => SmtResult.Unknown s!"{e}"

      trace[sauto.debug] "Test result: {checkSatResponse}"
      ret := ret ++ [((variablesInCheck, checkSatResponse))]
    trace[sauto.debug] "Results for all actions and invariants: {ret}"
    solver.kill
    return ret
  catch e =>
    let exMsg ← e.toMessageData.toString
    let mut ret := []
    for l in checks do
      let lefts := (l.map (fun (a, _) => a)).toList
      ret := ret ++ [(lefts, (.Unknown s!"{exMsg}"))]
    return ret
