import Lean.Elab.Tactic
import LeanSts.Tactic.Util
import LeanSts.TransitionSystem

-- For automation
import LeanSts.SMT.Main
import Duper

open Lean Lean.Elab.Tactic Meta.Tactic

/-- Destruct a structure into its fields.
    If no identifier is provided, destructs the goal. -/
elab "sdestruct " ids:(colGt ident)* : tactic => withMainContext do
  if ids.size == 0 then
    evalTactic $ ← `(tactic| repeat' constructor)
  else for id in ids do
    let lctx ← getLCtx
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

/-- Destruct all structures in the context into their respective fields. -/
elab "sdestruct_all" : tactic => withMainContext do
  let lctx ← getLCtx
  for hyp in lctx do
    let isStructure ← match hyp.type.getAppFn.constName? with
    | .none => pure false
    | .some sn => pure (isStructure (<- getEnv) sn)
    if isStructure then
      let name := mkIdent hyp.userName
      let dtac ← `(tactic| sdestruct $name:ident)
      evalTactic dtac

elab "sintro " ids:(colGt ident)* : tactic => withMainContext do
  evalTactic $ ← `(tactic| intro $(ids)* ; sdestruct $(ids)*)

elab "sts_induction" : tactic => withMainContext do
  -- (1) Identify the `next` hypothesis
  let opt_hnext ← (← getLCtx).findDeclM? fun (ldecl : Lean.LocalDecl) => do
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
  -- Create as many goals as `hnext` has constructors.
  -- For CIC-style systems, `.next` has the form `∃ (_t: [TransitionType]) True`,
  -- so we first destruct the existential quantifier.
  if ← normalisedIsAppOf hnext `Exists then
    evalTactic $ ←  `(tactic| rcases $hnextName:ident with ⟨$hnextName, _⟩)
  -- NOTE: context has changed, so we need this again
  withMainContext do
  -- (2) Destruct the `next` hypothesis into separate goals for each individual action
  -- We have two possibilities. Either:
  -- (a) `next` is a sequence of `∨`'ed propositions
  -- (b) `next` is an inductive type, in which case we can use `cases` to destruct it.
  if ← normalisedIsAppOf hnext `Or then
    -- FIXME: make sure we only break `Or`s, not other things
    let case_split ← `(tactic| repeat' (rcases $hnextName:ident with $hnextName | $hnextName))
    evalTactic case_split
  else -- TODO: check that this is an inductive type
    -- Inspired by `scase` in LeanSSR: https://github.com/verse-lab/lean-ssr/blob/29ba85c915de17602ba224558e6ebaf2a2845786/Ssreflect/Elim.lean#L11
    let oldHyps ← getLCtx
    evalTactic $ ← `(tactic| unhygienic cases $hnextName:ident)
    withMainContext $ allGoals $ do
    let newHyps ← newHypotheses oldHyps (← getLCtx)
    -- dbg_trace "newHyps: {newHyps.map (·.userName)}"
    assert! newHyps.size == 1
    let newHypName := mkIdent newHyps[0]!.userName
    evalTactic $ ← `(tactic| revert $newHypName:ident; intro $hnextName:ident)

/-- Solves a single-clause goal of the form `inv ∧ transition → inv_clause`. -/
elab "solve_clause" : tactic => withMainContext do
  -- (*) Collect tactics to generate suggestion
  let mut xtacs := #[]
  -- (1) Identify the type of the state
  let stateType ← findStateType (← getLCtx)
  let stateName := stateType.getAppFn.constName
  -- dbg_trace "State is structure with name: {stateName}"
  -- (2) Destruct all the state hypotheses into components
  for hyp in (← getLCtx) do
    if hyp.type == stateType then
      let name := mkIdent hyp.userName
      let dtac ← `(tactic| sdestruct $name:ident)
      xtacs := xtacs.push dtac
      evalTactic dtac
  -- (3) Simplify all invariants and transitions, as well as
  -- destruct structures into their components everywhere
  let injEqLemma := (mkIdent $ stateName ++ `mk ++ `injEq)
  -- dbg_trace "Using injEqLemma: {injEqLemma}"
  let simpTac ← `(tactic| simp only [actSimp, invSimp, $injEqLemma:ident] at *)
  xtacs := xtacs.push simpTac
  withMainContext do
  evalTactic simpTac
  -- (4) Identify:
  --   (a) all propositions in the context
  --   (b) all propositions within typeclasses in the context
  let mut props := #[]
  for hyp in (← getLCtx) do
    if hyp.isImplementationDetail then
      continue
    props := props.append (← collectPropertiesFromHyp hyp)
  -- (5) Call `auto` using these propositions
  -- dbg_trace "Props: {props}"
  -- If given duplicate terms, `auto` complains: "Auto does not accept duplicated input terms"
  let idents := (props.toList.eraseDups.map mkIdent).toArray
  let auto_tac ← `(tactic| auto [$[$idents:ident],*])
  let executed_tactics := (xtacs ++ #[auto_tac])
  trace[sauto] "{executed_tactics}"
  evalTactic auto_tac
