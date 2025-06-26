import Lean.Elab.Tactic
import Lean.Meta.Tactic.TryThis
import Veil.Util.Tactic
import Veil.Tactic.SplitIfs
import Veil.Model.TransitionSystem
import Veil.Theory.WP

-- For automation
import Veil.SMT.Main

open Lean Elab Tactic Meta Simp Tactic.TryThis

-- Copied from Mathlib's [`rename'` tactic ](https://github.com/leanprover-community/mathlib4/blob/25ffff65d07b0c88e418c1ecf26701808e521196/Mathlib/Tactic/Rename.lean#L22-L25)
syntax renameArg := term " => " ident
syntax (name := renameHyp) "rename_hyp " renameArg,+ : tactic

elab_rules : tactic
  | `(tactic| rename_hyp $[$as:term => $bs:ident],*) => do
    let ids ← getFVarIds as
    liftMetaTactic1 fun goal ↦ do
      let mut lctx ← getLCtx
      for fvar in ids, tgt in bs do
        lctx := lctx.setUserName fvar tgt.getId
      let mvarNew ← mkFreshExprMVarAt lctx (← getLocalInstances)
        (← goal.getType) MetavarKind.syntheticOpaque (← goal.getTag)
      goal.assign mvarNew
      pure mvarNew.mvarId!
    withMainContext do
      for fvar in ids, tgt in bs do
        Elab.Term.addTermInfo' tgt (mkFVar fvar)

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
    -- Try to give better names to the new hypotheses if they are named clauses
    withMainContext do
    let lctx ← getLCtx
    let spec := (<- localSpecCtx.get).spec
    let namedClauses := Std.HashSet.ofArray $ (spec.invariants ++ spec.assumptions).map (·.name)
    for hypIdent in newFieldNames do
      let name' := getNameOfIdent' hypIdent
      let .some ld := lctx.findFromUserName? name' | return
      let .some app := ld.type.getAppFn.constName? | return
      if namedClauses.contains app then
        let baseName := name.components[0]!
        let newName := mkIdent $ baseName ++ app
        evalTactic $ ← `(tactic| rename_hyp $hypIdent => $newName)

/-- Split the goal into sub-goals. -/
elab "sdestruct_goal" : tactic => withMainContext do
  evalTactic $ ← `(tactic| repeat' constructor)

instance : BEq LocalDecl := ⟨fun a b => a.userName == b.userName⟩


def veilSpecificNames : List Name := [``IsSubStateOf, ``IsSubReaderOf]

def hypIsVeilSpecific (hyp : LocalDecl) : TacticM Bool := do
  match hyp.type.getAppFn.constName? with
  | .none => pure false
  | .some sn =>
    return veilSpecificNames.contains sn

/-- Destruct all structures in the context into their respective fields,
recursively. Also destructs all existentials. -/
partial def elabSdestructHyps (recursive : Bool := false) (ignoreHyps : Array LocalDecl := #[]) : TacticM Unit := withMainContext do
  let mut ignoreHyps := ignoreHyps
  let hypsToVisit : (Array LocalDecl → TacticM (Array LocalDecl)) := (fun ignoreHyps => withMainContext do
    return (← getLCtx).decls.filter Option.isSome
    |> PersistentArray.map Option.get!
    |> PersistentArray.toArray
    |> Array.filter (fun hyp => !ignoreHyps.contains hyp))
  trace[debug] "[elabSdestructHyps] visit {(← hypsToVisit ignoreHyps).map (·.userName)}"
  for hyp in (← hypsToVisit ignoreHyps) do
    ignoreHyps := ignoreHyps.push hyp
    if hyp.isImplementationDetail then
      continue
    let isStructure ← match hyp.type.getAppFn.constName? with
    | .none => pure false
    | .some sn => pure (isStructure (<- getEnv) sn)
    let name := mkIdent hyp.userName
    if isStructure then
      let sn := hyp.type.getAppFn.constName!
      -- We don't want to destruct `IsSubStateOf` because it's needed
      -- to perform rewrites
      if !veilSpecificNames.contains sn then
        let dtac ← `(tactic| sdestruct $name:ident)
        evalTactic dtac
    else
      let isExists ← whnfIsAppOf hyp.type ``Exists
      if isExists then
        let lctx ← getLCtx
        -- we want the new hypotheses to have pick names so they're
        -- not included in the ignore list, hence we don't reuse `$name`
        let x := mkIdent $ lctx.getUnusedName (← existsBinderName hyp.type)
        let name' := mkIdent $ lctx.getUnusedName name.getId
        evalTactic $ ← `(tactic| rcases $name:ident with ⟨$x, $name'⟩)
  -- Recursively call ourselves until the context stops changing
  if recursive && (← hypsToVisit ignoreHyps).size > 0 then
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
  evalTactic $ ← `(tactic| try simp only [nextSimp] at $hnextName:ident)
  withMainContext do
  -- Destruct the `next` hypothesis into separate goals for each individual action
  -- We have two possibilities. Either:
  -- (a) `next` is a sequence of `∨`'ed propositions
  -- (b) `next` is an inductive type, in which case we can use `cases` to destruct it.
  if ← whnfIsAppOf hnext.type `Or then
    -- FIXME: make sure we only break `Or`s, not other things
    let case_split ← `(tactic| repeat' (rcases $hnextName:ident with $hnextName | $hnextName))
    evalTactic case_split
  else -- TODO: check that this is an inductive type
    -- Inspired by `scase` in LeanSSR: https://github.com/verse-lab/lean-ssr/blob/29ba85c915de17602ba224558e6ebaf2a2845786/Ssreflect/Elim.lean#L11
    let oldHyps ← getLCtx
    evalTactic $ ← `(tactic| unhygienic cases $hnextName:ident)
    withMainContext $ Tactic.allGoals $ do
    let newHyps ← newHypotheses oldHyps (← getLCtx)
    -- dbg_trace "newHyps: {newHyps.map (·.userName)}"
    assert! newHyps.size == 1
    let newHypName := mkIdent newHyps[0]!.userName
    evalTactic $ ← `(tactic| revert $newHypName:ident; intro $hnextName:ident)

/--
Get all the names of the propositions found in the context, including
within typeclasses in the context. This ignores some Veil-specific
typeclasses that should not be sent to the SMT solver.
-/
def getPropsInContext : TacticM (Array Ident) := do
  let mut props := #[]
  for hyp in (← getLCtx) do
    if hyp.isImplementationDetail || (← hypIsVeilSpecific hyp) then
      continue
    props := props.append (← collectPropertiesFromHyp hyp)
  let idents := (props.toList.eraseDups.map mkIdent).toArray
  return idents

def concatTacticSeq (xtacs : Array (TSyntax `Lean.Parser.Tactic.tacticSeq)) : TacticM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if xtacs.isEmpty then
    return ← `(tacticSeq|skip)
  let accInit ← `(tacticSeq|$(xtacs[0]!))
  let combined_tactic ← xtacs[1:].foldlM (init := accInit) fun acc tac => `(tacticSeq|
     ($acc)
     ($tac)
  )
  return combined_tactic

private inductive AbstractStateKind where
  /-- mutable state -/
  | state
  /-- immutable state / background theory -/
  | reader

def getAbstractStateHyps : TacticM (Array (AbstractStateKind × LocalDecl)) := withMainContext do
  let mut abstractStateHyps := #[]
  let lctx ← getLCtx
  for hyp in lctx do
    let `(term|$x:ident) ← delabWithMotives hyp.type
      | continue
    if x.getId == genericStateName then
      abstractStateHyps := abstractStateHyps.push (.state, hyp)
    else if x.getId == genericReaderName then
      abstractStateHyps := abstractStateHyps.push (.reader, hyp)
  return abstractStateHyps

def negElimLemmas := mkSimpLemmas $ #[``compl, ``Classical.not_imp, ``Classical.not_not, ``Classical.not_forall].map mkIdent

syntax concretizeState := "concretize_state" <|> "concretize_state?"
elab tk:concretizeState : tactic => withMainContext do
  let mut tacticsToPrint := #[]
-- Sometimes required to enable `subst`
  let doubleNegTac ← `(tacticSeq|try simp only [$negElimLemmas,*] at *; sdestruct_hyps)
  tacticsToPrint := tacticsToPrint.push doubleNegTac
  withMainContext $ evalTactic doubleNegTac
  for (_, s) in (← getAbstractStateHyps) do
    let tac ← `(tacticSeq| try subst $(mkIdent s.userName))
    if (← getUnsolvedGoals).length != 0 then
      tacticsToPrint := tacticsToPrint.push tac
      withMainContext $ evalTactic tac
  let mut (concretizeTacs, simpLemmaNames) := (#[], #[])
  -- NOTE: `subst` might have removed some of the abstract state hyps,
  -- so we need to recompute them
  for (k, hyp) in (← getAbstractStateHyps) do
    let simpLemmaName := mkIdent $ ← mkFreshBinderNameForTactic stateSimpHypName
    let concreteState := mkIdent $ hyp.userName
    let getter := match k with
    | .state => mkIdent ``getFrom
    | .reader => mkIdent ``readFrom
    let concretize ← `(tacticSeq|try rcases (@$(mkIdent ``exists_eq') _ ($(getter) $(mkIdent hyp.userName))) with ⟨$concreteState, $simpLemmaName⟩)
    concretizeTacs := concretizeTacs.push concretize
    simpLemmaNames := simpLemmaNames.push simpLemmaName

  let mut tacticsToExecute := #[]
  for t in concretizeTacs do tacticsToExecute := tacticsToExecute.push t
  let simpLemmas := mkSimpLemmas $ simpLemmaNames ++ [mkIdent `wpSimp]
  tacticsToExecute := tacticsToExecute.push $ ← `(tacticSeq|try simp only [$simpLemmas,*] at *)
  tacticsToExecute := tacticsToExecute.push $ ← `(tacticSeq|sdestruct_hyps; try simp only [smtSimp] at *)
  if let `(concretizeState| concretize_state?) := tk then
      tacticsToPrint := tacticsToPrint.append tacticsToExecute
      addSuggestion (<- getRef) (← concatTacticSeq tacticsToPrint)
      return
  for t in tacticsToExecute do
    if (← getUnsolvedGoals).length != 0 then
      withMainContext $ evalTactic t

def elabSimplifyClause (simp0 : Array Ident := #[`initSimp, `actSimp].map mkIdent) (thorough :  Bool := true) (traceAt : Option Syntax := none): TacticM (Array Ident × Array (TSyntax `Lean.Parser.Tactic.tacticSeq)) := withMainContext do
  -- (*) Collect executed tactics to generate suggestion
  let mut xtacs := #[]
  -- (1) Identify the type of the state
  let stateName ← getStateName
  -- dbg_trace "State is structure with name: {stateName}"
  -- (2) Destruct all hypotheses into components
  let destructTac ← `(tacticSeq| sdestruct_hyps)
  xtacs := xtacs.push destructTac
  evalTactic destructTac
  withMainContext do
  -- (3) Simplify all invariants and transitions, as well as
  -- destruct State structures into their components everywhere
  -- (for DSL-defined state, `injEqLemma` is included in `smtSimp`)
  -- We also make simplifications required by `lean-smt`: `funextEq`, `tupleEq`
  let injEqLemma := stateName ++ `mk ++ `injEq
  -- This is faster than `simp` with all the lemmas, see:
  -- https://github.com/verse-lab/lean-sts/issues/29#issuecomment-2360300222
  let simp0 := mkSimpLemmas simp0
  -- Doing a `thoroughSimp` is not needed when the actions have already been
  -- simplified, which is the case for DSL-defined actions
  let thoroughSimp := mkSimpLemmas $ #[injEqLemma, `invSimp, `smtSimp, `logicSimp].map mkIdent
  let fastSimp := mkSimpLemmas $ #[`invSimp, `smtSimp].map mkIdent
  let finalSimp := mkSimpLemmas $ #[`quantifierSimp].map mkIdent
  let simp2 := if thorough then thoroughSimp else fastSimp
  let simpTac ← `(tacticSeq|
    (try dsimp only [$simp0,*] at *)
    (try simp only [$simp2,*] at *)
    (try simp only [$finalSimp,*] at *)
    -- To get rid of `IsSubStateOf` applications
    (try concretize_state))
  let mut xtacs := xtacs.push simpTac
  withMainContext do
  evalTactic simpTac
  -- Sometimes the simplification solves the goal
  if (← getUnsolvedGoals).length == 0 then
    return ← finishWith #[] xtacs
  -- We destruct hypotheses again to eliminate any top-level `Exists` This also
  -- works around an issue where `lean-smt` somestimes introduces `And.left` and
  -- `And.right`.
  withMainContext do
  let mut xtacs := xtacs.push destructTac
  evalTactic destructTac
  -- (4) Identify:
  --   (a) all propositions in the context
  --   (b) all propositions within typeclasses in the context
  withMainContext do
  let idents ← getPropsInContext
  return ← finishWith idents xtacs
  where
  finishWith (idents : Array Ident) (xtacs : Array (TSyntax `Lean.Parser.Tactic.tacticSeq)) : TacticM (Array Ident × Array (TSyntax `Lean.Parser.Tactic.tacticSeq)) := do
    if let some stx := traceAt then
      let combined_tactic ← concatTacticSeq xtacs
      addSuggestion stx combined_tactic
    return (idents, xtacs)

syntax (name := simplifyClause) "simplify_clause" : tactic
syntax (name := simplifyClauseTrace) "simplify_clause?" : tactic
syntax (name := fastSimplifyClause) "fast_simplify_clause" : tactic
syntax (name := fastSimplifyClauseTrace) "fast_simplify_clause?" : tactic

elab_rules : tactic
  | `(tactic| simplify_clause%$_tk) => do _ ← elabSimplifyClause
  | `(tactic| simplify_clause?%$tk) => do _ ← elabSimplifyClause (traceAt := tk)
  | `(tactic| fast_simplify_clause%$_tk) => do _ ← elabSimplifyClause (thorough := false)
  | `(tactic| fast_simplify_clause?%$tk) => do _ ← elabSimplifyClause (thorough := false) (traceAt := tk)

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

/-- Clear all folded (i.e. not unfolded) invariants in the context. -/
elab "clear_folded_invariants" : tactic => withMainContext do
  let g : Array (Option Name) := (<- localSpecCtx.get).spec.invariants.map (·.name)
  let hyps <- getLCtx
  let hypsToClear := hyps.decls.toArray.filter (fun hyp =>
    match hyp with
    | some hyp => g.contains (hyp.type.getAppFn'.constName?)
    | none => false) |> Array.map (fun hyp => hyp.get!)
  -- logInfo s!"Clearing {hypsToClear.map (·.userName)}"
  for hyp in hypsToClear do
      evalTactic <| <- `(tactic| try clear $(mkIdent hyp.userName):ident)

def getInvariantsInSameIsolateAs (invInfo : StateAssertion) : TacticM (Array Ident) := do
  let mut invsToUnfold := #[]
  let isStore := (<- localSpecCtx.getIsolates).isolateStore
  unless invInfo.isolates.isEmpty do
    for is in invInfo.isolates do
      invsToUnfold := invsToUnfold.append <| isStore[is]!.toArray.map mkIdent
  return invsToUnfold

elab "enforce_isolate_for_invariant" inv:ident : tactic => withMainContext do
  let some invInfo := (<- localSpecCtx.get).spec.invariants.find? (·.name == inv.getId)
    | throwError "Invariant {inv.getId} not found"
  if !invInfo.isolates.isEmpty then
    let invSimpTopLevel := mkIdent `invSimpTopLevel
    let invsToUnfold := #[invSimpTopLevel] ++ (← getInvariantsInSameIsolateAs invInfo)
    -- logInfo s!"Enforcing isolate for invariant {inv.getId}; unfolding {invsToUnfold.map (·.getId)}"
    withMainContext do evalTactic $ ← `(tactic| dsimp only [$[$invsToUnfold:ident],*] at *)
    withMainContext do evalTactic $ ← `(tactic| clear_folded_invariants)


def handleInvariants (inv : Option Ident) : TacticM (TSyntax `tactic × TSyntax `tactic) := withMainContext do
  let mut invInfo := none
  if let some inv := inv then
    let some info := (<- localSpecCtx.get).spec.invariants.find? (mkIdent ·.name == inv)
      | throwError "Invariant {inv.getId} not found"
    invInfo := some info
  let (invSimp, invSimpTopLevel) := (mkIdent `invSimp, mkIdent `invSimpTopLevel)
  let (invSimpTac, clearInvs) ←
    if invInfo.all (·.isolates.isEmpty) then
      pure (← `(tactic| dsimp only [$invSimp:ident]), ← `(tactic| skip))
    else
      let invsToUnfold := #[invSimpTopLevel] ++ (← getInvariantsInSameIsolateAs invInfo.get!)
      pure (← `(tactic| dsimp only [$[$invsToUnfold:ident],*]), ← `(tactic| clear_folded_invariants))
  return (invSimpTac, clearInvs)

/-- Converts WP-style conditions to TR-style conditions, and vice-versa. -/
syntax swapMode := "swap_mode" <|> "swap_mode?"
elab tk:swapMode : tactic => withMainContext do
  let goal ← getMainTarget
  let tactic ← match_expr goal with
  | TwoState.meetsSpecificationIfSuccessful _ _ act _ _ =>
     -- get rid of the `.twoState` at the end
    let name := mkNameFromComponents act.getAppFn.constName.components.dropLast
    `(tactic| simp only [← $(mkIdent $ toEndToEndLemmaName name):ident, ← $(mkIdent ``VeilM.toTwoStateDerived_sound):ident, $(mkIdent ``TwoState.meetsSpecificationIfSuccessful_eq):ident])
  | VeilM.meetsSpecificationIfSuccessful _ _ _ _ act _ _ =>
    let name := act.getAppFn.constName
    `(tactic| simp only [$(mkIdent $ toEndToEndLemmaName name):ident, $(mkIdent ``VeilM.toTwoStateDerived_sound):ident, ← $(mkIdent ``TwoState.meetsSpecificationIfSuccessful_eq):ident])
  | _ =>
    throwError "Goal does not consist of a `meetsSpecificationIfSuccessful` application"
  let showSuggestion := if let `(swapMode| swap_mode?) := tk then true else false
  if showSuggestion then
    addSuggestion (<- getRef) tactic
  evalTactic tactic

def elabAlreadyProven (trName : Name) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← g.getType
  let ty ← instantiateMVars ty
  let inv := ty.getAppFn'
  let .some (invName, _) := inv.const? | throwError "the goal {ty} is not about an invariant clause? got {inv}, expect it to be a const"
  let thmName := mkTrTheoremName (dropSuffixes trName) invName
  if trName == initializerName then
    let initHypName := `hinit
    let .some _ := (← getLCtx).findFromUserName? initHypName| throwError "cannot find {initHypName}!"
    let destructTac ← `(tactic| rcases $(mkIdent initHypName):ident with ⟨_, ⟨$(mkIdent `st0):ident, $(mkIdent initHypName):ident⟩⟩)
    trace[veil.debug] "destructTac: {destructTac}"
    evalTactic destructTac
  withMainContext do
    let attempt ← `(tactic| (apply $(mkIdent thmName) <;> ((try simp_all) <;> assumption)) )
    trace[veil.debug] "attempt: {attempt}"
    evalTactic attempt

elab "already_proven_init" : tactic => elabAlreadyProven initializerName

open Tactic in
elab "already_proven_next_tr" : tactic => withMainContext do
  let .some ld := (← getLCtx).findFromUserName? `hnext | throwError "cannot find hnext!"
  let tr := ld.type.getAppFn'
  let .some (trName, _) := tr.const? | throwError "hnext is not a premise about .tr? got {tr}, expect it to be a .tr"
  elabAlreadyProven trName

syntax solveTr := "solve_tr_clause" <|> "solve_tr_clause?"
elab tk:solveTr act:ident inv:ident : tactic => withMainContext do
  let (invSimpTac, clearInvs) ← handleInvariants inv
  let ifSimp := mkIdent `ifSimp
  let simplify <- `(tacticSeq|
    try dsimp only [$(mkIdent ``TwoState.meetsSpecificationIfSuccessful):ident, $(mkIdent ``TwoState.triple):ident]
    dsimp only [$act:ident]
    $invSimpTac:tactic
    unhygienic intros
    sdestruct_hyps
    try simp only [$ifSimp:ident] at *
    sdestruct_hyps
    $clearInvs:tactic
  )
  let finisher ← `(Parser.Tactic.tacticSeqBracketed|{
    try concretize_state
    sauto_all
  })
  let solve <- `(tacticSeq|(try unhygienic split_ifs at *) <;> ($finisher:tacticSeqBracketed))
  if let `(solveTr| solve_tr_clause?) := tk then
      addSuggestion (<- getRef) (← concatTacticSeq #[simplify, solve])
  else
    -- act is something like either `initializer.ext.twoState` or `Ring.recv.ext.twoState`
    let wpTheoremName := mkIdent $ mkTheoremName (dropSuffixes act.getId) inv.getId
    let tryLift ← `(tactic| try (intros; swap_mode; apply $wpTheoremName))
    trace[veil.debug] "tryLift (from wp to tr): {tryLift}"
    evalTactic tryLift
    if (← getUnsolvedGoals).length == 0 then
      return
    evalTactic simplify
    if (← getUnsolvedGoals).length != 0 then
      withMainContext do
        evalTactic solve

syntax solveWp := "solve_wp_clause" <|> "solve_wp_clause?"
elab tk:solveWp act:ident inv:ident ? : tactic => withMainContext do
  let (invSimpTac, clearInvs) ← handleInvariants inv
  let introExId <- if inv.isNone then `(tactic| intro $(mkIdent `exId):ident) else `(tactic| skip)
  let (wpSimp, rd, st, st', ass, inv_, ifSimp, and_imp, exists_imp) :=
      (mkIdent `wpSimp,
       mkIdent `rd,
       mkIdent `st, mkIdent `st',
       mkIdent `ass_, mkIdent `inv_,
       mkIdent `ifSimp,
       mkIdent `exists_imp,
       mkIdent `and_imp)
  let stateTpT ← getStateTpStx
  let name := act.getId
  let actSimp := mkSimpLemmas $ #[toWpLemmaName name, toWpSuccLemmaName name, toWpSuccName name ].map mkIdent
  let simplify <- `(tacticSeq|
    try simp only [$(mkIdent ``VeilM.meetsSpecificationIfSuccessful):ident, $(mkIdent ``triple):ident, $(mkIdent ``LE.le):ident, $(mkIdent ``and_imp):ident]
    -- this is for regular clauses
    try simp only [$actSimp,*]
    -- this is for termination (`.wpEx` clauses)
    try dsimp only [$act:ident, $wpSimp:ident]
    $invSimpTac:tactic
    $introExId
    intros $rd:ident $st:ident; sdestruct_hyps
    first
      -- This is for actions defined via transitions
      | intro $ass:ident $inv_:ident; intro ($st':ident : $stateTpT);
        unhygienic cases $st':ident; revert $ass:ident $inv_:ident; dsimp only
      | try dsimp only
        try simp only [$and_imp:ident, $exists_imp:ident]
        unhygienic intros
        $clearInvs:tactic
        try simp only [$ifSimp:ident]
        try sdestruct_hyps
        try dsimp only at *
        try concretize_state
        )
    let solve <- `(tacticSeq| (try split_ifs with $and_imp, $exists_imp) <;> sauto_all)
    if let `(solveWp| solve_wp_clause?) := tk then
      addSuggestion (<- getRef) (← concatTacticSeq #[simplify, solve])
    else
      -- act is something like either `initializer.ext.twoState` or `Ring.recv.ext.twoState`
      if let .some inv := inv then
        let trTheoremName := mkIdent $ mkTrTheoremName (dropSuffixes act.getId) inv.getId
        let tryLift ← `(tactic| try (intros; swap_mode; apply $trTheoremName))
        trace[veil.debug] "tryLift (from tr to wp): {tryLift}"
        evalTactic tryLift
        if (← getUnsolvedGoals).length == 0 then
          return
      evalTactic simplify
      -- Simplification might solve the goal; if we try to evaluate `sauto_all` in
      -- that case, this will wrongly throw an error, which might confuse the user.
      if (← getUnsolvedGoals).length != 0 then
        withMainContext do
          evalTactic solve

def elabSolveClause (stx : Syntax)
  (simp0 : Array Ident := #[`initSimp, `actSimp].map mkIdent)
  (inv : Option Name := none)
  (trace : Bool := false) : TacticM Unit := withMainContext do
  withTraceNode `veil.smt.perf.solveClause (fun _ => return "solve_clause") do
  if let some inv := inv then
    let enforceIsolate ← `(tactic|simp only [invSimpTopLevel] at *; sdestruct_hyps; enforce_isolate_for_invariant $(mkIdent inv))
    evalTactic enforceIsolate
  let (idents, xtacs) ← elabSimplifyClause (simp0 ++ [mkIdent `wpSimp])
  -- Sometimes the simplification solves the goal, and we don't need to
  -- `sauto`; this check needs to be before `withMainContext`, since that
  -- calls `throwNoGoalsToBeSolved` if there are no goals.
  if (← getUnsolvedGoals).length != 0 then
    withMainContext do
      let autoTac ← `(tacticSeq| sauto [$[$idents:ident],*])
      if trace then
        addSuggestion stx (← concatTacticSeq (xtacs.push autoTac))
      evalTactic autoTac
  else
    if trace then
      addSuggestion stx (← concatTacticSeq xtacs)

syntax (name := solveClause) "solve_clause" : tactic
syntax (name := solveClauseTrace) "solve_clause?" : tactic

/-- In square brackets are the action names (or simp sets like
`initSimp` and `actSimp`) to be unfolded, and following that is the
invariant/clause name to be proven. The latter is used to enforce
isolates as well. -/
syntax (name := solveClauseWith) (solveClause <|> solveClauseTrace) "[" ident,* "]" ident : tactic
elab_rules : tactic
  | `(tactic| solve_clause%$tk) => elabSolveClause tk
  | `(tactic| solve_clause?%$tk) => elabSolveClause tk (trace := true)
  | `(tactic| solve_clause%$tk [ $[$simp0],* ] $inv:ident)   => elabSolveClause tk simp0 inv.getId
  | `(tactic| solve_clause?%$tk [ $[$simp0],* ] $inv:ident)   => elabSolveClause tk simp0 inv.getId (trace := true)

elab "simplify_all" : tactic => withMainContext do
  let toDsimp := mkSimpLemmas $ #[`initSimp, `actSimp, `invSimp, `safeSimp, `smtSimp, `logicSimp].map mkIdent
  let toSimp := mkSimpLemmas $ #[`smtSimp, `logicSimp].map mkIdent
  let finalSimp := mkSimpLemmas $ #[`quantifierSimp].map mkIdent
  let simp_tac ← `(tactic|
    (try dsimp only [$toDsimp,*] at *) ;
    (try simp only [$toSimp,*] at *);
    (try simp only [$finalSimp,*] at *))
  trace[veil.debug] "simp_tac: {simp_tac}"
  evalTactic simp_tac

/-- Tactic to solve `unsat trace` goals. -/
elab "bmc" : tactic => withMainContext do
  let tac ← `(tactic|
    (try simp only [initSimp, nextSimp, actSimp, invSimp]); (try simplify_all);
    (unhygienic intros);
    sdestruct_hyps;
    (try simplify_all);
    -- FIXME: workaround for `lean-smt` introducing `And.left` and `And.right`
    sdestruct_hyps;
    (try simplify_all);
    sauto_all
  )
  trace[veil.smt] "{tac}"
  evalTactic $ tac

open Lean.Meta in
def bmcSat : TacticM Unit := withMainContext do
  let originalGoal ← Tactic.getMainGoal
  -- Operate on a duplicated goal
  let goal' ← mkFreshExprMVar (← Tactic.getMainTarget)
  replaceMainGoal [goal'.mvarId!]
  run `(tactic| simp only [initSimp, nextSimp, actSimp, invSimp]; simplify_all)
  if (← getUnsolvedGoals).length == 0 then
    originalGoal.admit (synthetic := false)
  else
    existIntoForall
    let simpLemmas := mkSimpLemmas $ #[`smtSimp].map mkIdent
    withMainContext do run `(tactic| unhygienic intros; sdestruct_hyps; (try simp only [$simpLemmas,*]))
    if (← getUnsolvedGoals).length == 0 then
      originalGoal.admit (synthetic := false)
    else
      admitIfSat
      if (← getUnsolvedGoals).length == 0 then
        originalGoal.admit (synthetic := false)
      else
        throwError "goal is not solved by SMT"
where
  existIntoForall := withMainContext do
    let goalType' ← turnExistsIntoForall (← Tactic.getMainTarget)
    let goal' ← mkFreshExprMVar goalType'
    replaceMainGoal [goal'.mvarId!]
  /-- UNSAFE: admits the goal if it is satisfiable, taking into account
  all hypotheses in the context. -/
  admitIfSat : TacticM Unit := withMainContext do
  let opts ← getOptions
  let mv ← Tactic.getMainGoal
  let idents ← getPropsInContext
  let hints ← `(Smt.Tactic.smtHints|[$[$idents:ident],*])
  let hs ← Smt.Tactic.elabHints ⟨hints⟩
  let withTimeout := veil.smt.timeout.get opts
  -- IMPORTANT: `prepareLeanSmtQuery` (in `Smt.prepareSmtQuery`) negates
  -- the goal (it's designed for validity checking), so we negate it here
  -- to counter-act this.
  -- NOTE: we don't respect `veil.smt.translator` here, since we want to
  -- print a readable model, which requires `lean-smt`.
  let mv' ← mkFreshExprMVar (mkNot $ ← Tactic.getMainTarget)
  let leanSmtQueryString ← Veil.SMT.prepareLeanSmtQuery mv'.mvarId! hs
  let (res, solverUsed) ← Veil.SMT.querySolver leanSmtQueryString withTimeout (retryOnUnknown := true)
  match res with
  | .Sat .none => mv.admit (synthetic := false)
  | .Sat (some modelString) =>
    -- try to generate a readable model, using `lean-smt`
    let resStr := match ← Veil.SMT.getReadableModel leanSmtQueryString withTimeout (minimize := veil.smt.model.minimize.get opts) with
    | .some fostruct => s!"{fostruct}"
    | .none => s!"(could not get readable model)\n{modelString}"
    logInfo resStr
    mv.admit (synthetic := false)
  | .Unknown reason => throwError "{Veil.SMT.unknownGoalStr solverUsed}{if reason.isSome then s!": {reason.get!}" else ""}"
  | .Failure reason => throwError "{Veil.SMT.failureGoalStr solverUsed}{if reason.isSome then s!": {reason.get!}" else ""}"
  | .Unsat => throwError "{Veil.SMT.satGoalStr solverUsed}"

/-- Tactic to solve `sat trace` goals.

Given a goal of the form `∃ x, P x` (valid), we prove it by showing `P c`
is _satisfiable_ for some constant `c`.

In principle, we could use the model returned by the SMT solver to
instantiate the existential quantifiers, and thus avoid the need to
trust the solver, but this is not implemented yet.
-/
elab "bmc_sat" : tactic => bmcSat
