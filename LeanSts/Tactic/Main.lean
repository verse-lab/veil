import Lean.Elab.Tactic
import LeanSts.Tactic.Util
import LeanSts.TransitionSystem
import Lean.Meta.Tactic.TryThis

-- For automation
import LeanSts.SMT.Main
import Duper

open Lean Elab Tactic Meta Simp Tactic.TryThis

/-- Destruct a structure into its fields. -/
elab "sdestruct " ids:(colGt ident)* : tactic => withMainContext do
  if ids.size == 0 then
    throwError "sdestruct: no identifier provided"
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

/-- Split the goal into sub-goals. -/
elab "sdestruct_goal" : tactic => withMainContext do
  evalTactic $ ← `(tactic| repeat' constructor)

instance : BEq LocalDecl := ⟨fun a b => a.userName == b.userName⟩

/-- Destruct all structures in the context into their respective fields, recursively. -/
partial def elabSdestructHyps (recursive : Bool := false) (ignoreHyps : Array LocalDecl := #[]) : TacticM Unit := withMainContext do
  let mut ignoreHyps := ignoreHyps
  let hypsToVisit := (← getLCtx).decls.filter Option.isSome
    |> PersistentArray.map Option.get!
    |> PersistentArray.toArray
    |> Array.filter (fun hyp => !ignoreHyps.contains hyp)
  for hyp in hypsToVisit do
    ignoreHyps := ignoreHyps.push hyp
    let isStructure ← match hyp.type.getAppFn.constName? with
    | .none => pure false
    | .some sn => pure (isStructure (<- getEnv) sn)
    if isStructure then
      let name := mkIdent hyp.userName
      let dtac ← `(tactic| sdestruct $name:ident)
      evalTactic dtac
  -- Recursively call ourselves until the context stops changing
  if recursive && hypsToVisit.size > 0 then
    elabSdestructHyps recursive ignoreHyps

/-- Recursively destruct hypotheses. -/
syntax "sdestruct_hyps" : tactic
elab_rules : tactic
  | `(tactic| sdestruct_hyps) => elabSdestructHyps (recursive := true)

/-- Destruct the goal and all hypotheses. -/
elab "sdestruct_all" : tactic => withMainContext do
  evalTactic $ ← `(tactic| sdestruct_hyps ; sdestruct_goal )

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

/-- Get all the names of the propositions found in the context, including
    within typeclasses in the context. -/
def getPropsInContext : TacticM (Array Ident) := do
  let mut props := #[]
  for hyp in (← getLCtx) do
    if hyp.isImplementationDetail then
      continue
    props := props.append (← collectPropertiesFromHyp hyp)
  let idents := (props.toList.eraseDups.map mkIdent).toArray
  return idents

/--
  `simp0` is an optimisation to speed up the simplification process.
  For instance, if we know that the goal is an `init` goal, we can
  pass ``#[`initSimp]`` to not waste time simplifying actions.
-/
def elabSolveClause (stx : Syntax)
  (simp0 : Array Ident := #[`initSimp, `actSimp].map mkIdent)
  (trace : Bool := false) : TacticM Unit := withMainContext do
  -- (*) Collect executed tactics to generate suggestion
  let mut xtacs := #[]
  -- (1) Identify the type of the state
  let stateType ← findStateType (← getLCtx)
  let stateName := stateType.getAppFn.constName
  -- dbg_trace "State is structure with name: {stateName}"
  -- (2) Destruct all hypotheses into components
  let destructTac ← `(tactic| sdestruct_hyps)
  xtacs := xtacs.push destructTac
  evalTactic destructTac
  withMainContext do
  -- (3) Simplify all invariants and transitions, as well as
  -- destruct State structures into their components everywhere (via `injEqLemma`)
  -- We also make simplifications required by `lean-smt`: `funextEq`, `tupleEq`
  let injEqLemma := stateName ++ `mk ++ `injEq
  -- This is faster than `simp` with all the lemmas, see:
  -- https://github.com/verse-lab/lean-sts/issues/29#issuecomment-2360300222
  let simp0 := mkSimpLemmas simp0
  -- the `actSimp here is used for function calls under wlp
  let simp1 := mkSimpLemmas $ #[`wlp, `actSimp].map mkIdent
  let simp2 := mkSimpLemmas $ #[injEqLemma, `invSimp, `smtSimp].map mkIdent
  let simpTac ← `(tactic| try (try dsimp only [$simp0,*] at *) ; (try simp only [$simp2,*] at *))
  let mut xtacs := xtacs.push simpTac
  withMainContext do
  evalTactic simpTac
  -- (4) Identify:
  --   (a) all propositions in the context
  --   (b) all propositions within typeclasses in the context
  let idents ← getPropsInContext
  -- (5) Call `sauto` using these propositions
  let autoTac ← `(tactic| sauto [$[$idents:ident],*])
  let mut xtacs := xtacs
  -- Sometimes the simplification solves the goal, and we don't need to `sauto`
  if (← getUnsolvedGoals).length != 0 then
    xtacs := xtacs.push autoTac
  if trace then
    -- FIXME: the indentation is wrong for the `sauto` tactic
    let combined_tactic ← `(tactic| $xtacs;*)
    addSuggestion stx combined_tactic
  if (← getUnsolvedGoals).length != 0 then
    evalTactic autoTac

syntax (name := solveClause) "solve_clause" : tactic
syntax (name := solveClauseWith) "solve_clause" "[" ident,* "]" : tactic
syntax (name := solveClauseTrace) "solve_clause?" : tactic
elab_rules : tactic
  | `(tactic| solve_clause%$tk) => elabSolveClause tk
  | `(tactic| solve_clause?%$tk) => elabSolveClause tk (trace := true)
  | `(tactic| solve_clause%$tk [ $[$simp0],* ]) => elabSolveClause tk simp0

/-- Call `sauto` with all the hypotheses in the context. -/
def elabSautoAll (stx : Syntax) (trace : Bool := false) : TacticM Unit := withMainContext do
  let idents ← getPropsInContext
  let auto_tac ← `(tactic| sauto [$[$idents:ident],*])
  if trace then
    addSuggestion stx auto_tac
  evalTactic auto_tac

syntax (name := sautoAll) "sauto_all" : tactic
syntax (name := sautoAllTrace) "sauto_all?" : tactic
elab_rules : tactic
  | `(tactic| sauto_all%$tk) => elabSautoAll tk
  | `(tactic| sauto_all?%$tk) => elabSautoAll tk true

elab "simplify_all" : tactic => withMainContext do
  -- FIXME: why does `simp only [actSimp, wlp]` loop?
  let toDsimp := mkSimpLemmas $ #[`initSimp, `actSimp, `wlp, `invSimp, `safeSimp, `smtSimp].map mkIdent
  let toSimp := mkSimpLemmas $ #[`smtSimp].map mkIdent
  let simp_tac ← `(tactic| dsimp only [$toDsimp,*] at * ; simp only [$toSimp,*];)
  evalTactic simp_tac

/-- Tactic to solve `unsat trace` goals. -/
elab "bmc" : tactic => withMainContext do
  let tac ← `(tactic|
    (unhygienic intros);
    sdestruct_hyps;
    simplify_all;
    sauto_all
  )
  trace[sauto] "{tac}"
  evalTactic $ tac

/-- Tactic to solve `sat_trace` goals. -/
elab "bmc_sat" : tactic => withMainContext do
  let prep_tac ← `(tactic|
    negate_goal;
    simp only [Classical.exists_elim, Classical.not_not];
    (unhygienic intros);
    sdestruct_hyps;
    simplify_all;
    /- Needed to work around [lean-smt#100](https://github.com/ufmg-smite/lean-smt/issues/100) -/
    rename_binders
  )
  trace[sauto] "{prep_tac}"
  evalTactic prep_tac
  /- After preparing the context, call `sauto` on it. -/
  withMainContext do
  let idents ← getPropsInContext
  let auto_tac ← `(tactic| admit_if_satisfiable [$[$idents:ident],*])
  trace[sauto] "{auto_tac}"
  evalTactic auto_tac
