import Lean
import Auto
import Veil.SMT.Imports

import Veil.SMT.Base

namespace Veil.SMT

open Lean Elab Tactic Meta Qq in
def prepareLeanSmtQuery (mv' : MVarId) (hs : List Expr) : MetaM String := do
  -- HACK: We operate on a cloned goal, and then reset it to the original.
  let mv := (← mkFreshExprMVar (← mv'.getType)).mvarId!
  mv.withContext do
    withTraceNode `veil.smt.perf.translate (fun _ => return "prepareQuery") do
    Smt.withProcessedHints mv hs fun mv hs => mv.withContext do
    let (hs, mv) ← Smt.Preprocess.elimIff mv hs
    mv.withContext do
    let goalType : Q(Prop) ← mv.getType
    -- 2. Generate the SMT query.
    let (fvNames₁, _fvNames₂) ← Smt.genUniqueFVarNames
    let cmds ← Smt.prepareSmtQuery hs goalType fvNames₁
    let cmdString := s!"{Smt.Translate.Command.cmdsAsQuery cmds}"
    trace[veil.smt.debug] "goal:\n{goalType}"
    trace[veil.smt] "query:\n{cmdString}"
    return cmdString

open Lean Elab Tactic Meta Auto in
/-- Alternative to `prepareLeanSmtQuery`, this invokes `lean-auto` to generate the
  SMT query rather than `lean-smt`. The advantage is this is much faster
  (see
  [ufmg-smite#126](https://github.com/ufmg-smite/lean-smt/issues/126)),
  but produces unreadable queries. -/
def prepareLeanAutoQuery (mv : MVarId) (hints : TSyntax `Auto.hints) : TacticM String := do
  withTraceNode `veil.smt.perf.translate (fun _ => return "prepareAutoQuery") do
  -- HACK: We operate on a cloned goal, and then reset it to the original.
  let goal := (← mkFreshExprMVar (← mv.getType)).mvarId!
  let (goalBinders, newGoal) ← goal.intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "prepareAutoQuery :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let (lemmas, inhFacts) ← collectAllLemmas hints #[] (goalBinders.push ngoal)
    let query ← getQueryFromAuto lemmas inhFacts
    -- IMPORTANT: Reset the goal to the original
    replaceMainGoal [mv]
    return query
  where
  -- based on `runAuto`
  getQueryFromAuto
    (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM String := do
    -- Simplify `ite`
    let ite_simp_lem ← Lemma.ofConst ``Auto.Bool.ite_simp (.leaf "hw Auto.Bool.ite_simp")
    let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem ite_simp_lem)
    -- Simplify `decide`
    let decide_simp_lem ← Lemma.ofConst ``Auto.Bool.decide_simp (.leaf "hw Auto.Bool.decide_simp")
    let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem decide_simp_lem)
    let afterReify (uvalids : Array UMonoFact) (uinhs : Array UMonoFact) (minds : Array (Array SimpleIndVal)) : LamReif.ReifM String := (do
      let exportFacts ← LamReif.reifFacts uvalids
      let mut exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
      let _ ← LamReif.reifInhabitations uinhs
      let exportInds ← LamReif.reifMutInds minds
      LamReif.printValuation
      -- **Preprocessing in Verified Checker**
      let (exportFacts', exportInds) ← LamReif.preprocess exportFacts exportInds
      exportFacts := exportFacts'
      getAutoQueryString exportFacts exportInds)
    let (cmdString, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM String) do
      let s ← get
      let u ← computeMaxLevel s.facts
      (afterReify s.facts s.inhTys s.inds).run' {u := u})
    return cmdString
  getAutoQueryString (exportFacts : Array Embedding.Lam.REntry) (exportInds : Array Embedding.Lam.MutualIndInfo) : LamReif.ReifM String := do
    let lamVarTy := (← LamReif.getVarVal).map Prod.snd
    let lamEVarTy ← LamReif.getLamEVarTy
    let exportLamTerms ← exportFacts.mapM (fun re => do
      match re with
      | .valid [] t => return t
      | _ => throwError "runAuto :: Unexpected error")
    let sni : SMT.SMTNamingInfo :=
      {tyVal := (← LamReif.getTyVal), varVal := (← LamReif.getVarVal), lamEVarTy := (← LamReif.getLamEVarTy)}
    let ((commands, _validFacts), _state) ← (lamFOL2SMT sni lamVarTy lamEVarTy exportLamTerms exportInds).run
    trace[debug] "{_state.h2lMap.toArray}"
    let queryStr := String.intercalate "\n" (commands.toList.map toString)
    return queryStr

end Veil.SMT
