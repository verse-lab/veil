import Lean
import Veil.Frontend.DSL.Infra.State
import Veil.Frontend.DSL.Module.Util
import Veil.Util.Meta
import Smt
import Veil.Backend.SMT.Preprocessing
import Veil.Backend.SMT.Quantifiers

open Lean Elab Tactic Meta Simp Tactic.TryThis Parser.Tactic
namespace Veil

/-- A wrapper around Lean's standard `evalTactic`. ALWAYS use this instead of
`evalTactic`.

This has two purposes:
  - it uses `withoutRecover`, ensuring errors/exceptions are not silently swallowed
  - it performs Veil-specific logging when `isDesugared` is `true`

We set `isDesugared` to `false` when we are calling `evalTactic` _on_ a
Veil-specific tactic — i.e. tactics which are sugar for other tactics. -/
def veilEvalTactic (stx : Syntax) (isDesugared : Bool := true) : Tactic.TacticM Unit := do
  if isDesugared then
    trace[veil.desugar] "{stx}"
  -- The `withoutRecover` ensures errors/exceptions are not silently swallowed
  withoutRecover $ Tactic.evalTactic stx


/-- Like `withMainContext`, but does nothing if there are no unsolved goals (as
opposed to throwing a "no goals to be solved" error). -/
def veilWithMainContext [Inhabited α](tac : Tactic.TacticM α) : Tactic.TacticM α := do
  if (← getUnsolvedGoals).length != 0 then
    withMainContext tac
  else
    return default

def stateSimpHypName : Name := `hStateSimp

instance : BEq LocalDecl := ⟨fun a b => a.userName == b.userName⟩


syntax renameArg := term " => " ident
/-- Renames one or more hypotheses. Usage:

```lean
veil_rename_hyp old_name => new_name
```
-/
syntax (name := veil_rename_hyp) "veil_rename_hyp " renameArg,+ : tactic
/-- Clear the given hypotheses, as well as all Veil-specific hypotheses
which are not needed for proofs. -/
syntax (name := veil_clear) "veil_clear" (colGt ident)* : tactic
/-- Destruct the given structures into their fields. If no arguments
are given, this destructs all structures in the context into their
respective fields, recursively. -/
syntax (name := veil_destruct) "veil_destruct" (colGt ident)* : tactic
/-- Split the goal into sub-goals. -/
syntax (name := veil_destruct_goal) "veil_destruct_goal" : tactic

syntax (name := veil_concretize_state) "veil_concretize_state" : tactic
syntax (name := veil_concretize_fields) "veil_concretize_fields" : tactic

syntax (name := veil_intros) "veil_intros" : tactic
syntax (name := veil_fol) "veil_fol" : tactic

syntax (name := veil_simp) "veil_simp" simpTraceArgsRest : tactic
syntax (name := veil_simp_trace) "veil_simp?" simpTraceArgsRest : tactic

syntax (name := veil_wp) "veil_wp" : tactic

syntax (name := veil_smt) "veil_smt" : tactic
syntax (name := veil_smt_trace) "veil_smt?" : tactic

syntax (name := veil_if) "veil_split_ifs" : tactic
syntax (name := veil_solve) "veil_solve" : tactic

/-- Tactic for debugging purposes. Just throws an error. -/
syntax (name := veil_fail) "veil_fail" : tactic

attribute [ifSimp] ite_true ite_false dite_true dite_false ite_self
  if_true_left if_true_right if_false_left if_false_right

def elabVeilRenameHyp (xs ys : Array Syntax) := do
  let ids ← getFVarIds xs
  liftMetaTactic1 fun goal ↦ do
    let mut lctx ← getLCtx
    for fvar in ids, tgt in ys do
      lctx := lctx.setUserName fvar tgt.getId
    let mvarNew ← mkFreshExprMVarAt lctx (← getLocalInstances)
      (← goal.getType) MetavarKind.syntheticOpaque (← goal.getTag)
    goal.assign mvarNew
    pure mvarNew.mvarId!
  veilWithMainContext do
    for fvar in ids, tgt in ys do
      Elab.Term.addTermInfo' tgt (mkFVar fvar)

/-- Hypotheses which should not be touched by our tactics and which
should not be sent to the SMT solver. -/
def hypsToIgnore : List Name := [``IsSubReaderOf, ``IsSubStateOf,
  ``Inhabited, ``Nonempty, ``DecidableEq, ``Decidable, ``FieldRepresentation, ``LawfulFieldRepresentation]

/-- Get all the names of the propositions found in the context. This
ignores some Veil-specific typeclasses that should not be sent to the
SMT solver. -/
def getPropsInContext : TacticM (Array Ident) := do
  let mut props := #[]
  for hyp in (← getLCtx) do
    if hyp.isImplementationDetail || (← hypShouldBeIgnored hyp) then
      continue
    -- TODO: go inside hypotheses as well (`collectPropertiesFromHyp`)
    props := props.push hyp.userName
  let idents := (props.toList.eraseDups.map mkIdent).toArray
  return idents
  where
    hypShouldBeIgnored (hyp : LocalDecl) : TacticM Bool := do
      let isIgnored := match hyp.type.getForallBody.getAppFn.constName? with
        | .none => false
        | .some sn => hypsToIgnore.contains sn
      let typ ← whnf hyp.type
      let isInhabitationFact := (typ.isAppOf ``Nonempty) || (typ.isAppOf ``Inhabited)
      let isProp ← Meta.isProp typ
      return isIgnored || isInhabitationFact || !isProp

mutual

/-- Destruct a structure into its fields. -/
partial def elabVeilDestructSpecificHyp (ids : Array (TSyntax `ident)) : TacticM Unit := veilWithMainContext do
  if ids.size == 0 then
    elabVeilDestructAllHyps (recursive := true)
  else for id in ids do
    let lctx ← getLCtx
    let name := (getNameOfIdent' id)
    let .some ld := lctx.findFromUserName? name | throwError "veil_destruct: {id} is not in the local context"
    let .some sn := ld.type.getAppFn.constName? | throwError "veil_destruct: {id} is not a constant"
    let .some _sinfo := getStructureInfo? (← getEnv) sn | throwError "veil_destruct: {id} ({sn} is not a structure)"
    let newFieldNames := _sinfo.fieldNames.map (mkIdent $ Name.append name ·)
    let s ← `(rcasesPat| ⟨ $[$newFieldNames],* ⟩)
    veilEvalTactic $ ← `(tactic| unhygienic rcases $(mkIdent ld.userName):ident with $s)
    -- TODO: try to give better names to the new hypotheses if they are named clauses

/-- Destruct all structures in the context into their respective
fields, (potentially) recursively. Also destructs all existentials. -/
partial def elabVeilDestructAllHyps (recursive : Bool := false) (ignoreHyps : Array LocalDecl := #[]) : TacticM Unit := veilWithMainContext do
  let mut ignoreHyps := ignoreHyps
  let hypsToVisit : (Array LocalDecl → TacticM (Array LocalDecl)) := (fun ignoreHyps => veilWithMainContext do
    return (← getLCtx).decls.filter Option.isSome
    |> PersistentArray.map Option.get!
    |> PersistentArray.toArray
    |> Array.filter (fun hyp => !ignoreHyps.contains hyp))
  for hyp in (← hypsToVisit ignoreHyps) do
    ignoreHyps := ignoreHyps.push hyp
    if hyp.isImplementationDetail then
      continue
    let isStructure ← match hyp.type.getAppFn.constName? with
    | .none => pure false
    | .some sn => pure (isStructure (← getEnv) sn)
    let name := mkIdent hyp.userName
    if isStructure then
      let sn := hyp.type.getAppFn.constName!
      if !hypsToIgnore.contains sn then
        let dtac ← `(tactic| veil_destruct $name:ident)
        veilEvalTactic dtac (isDesugared := false)
    else
      let hypType ← Meta.whnf hyp.type
      if hypType.isAppOf ``Exists then
        let lctx ← getLCtx
        -- we want the new hypotheses to have fresh names so they're
        -- not included in the ignore list, hence we don't reuse `$name`
        let x := mkIdent $ lctx.getUnusedName (← existsBinderName hyp.type)
        let name' := mkIdent $ lctx.getUnusedName name.getId
        veilEvalTactic $ ← `(tactic| rcases $name:ident with ⟨$x, $name'⟩)
  -- Recursively call ourselves until the context stops changing
  if recursive && (← hypsToVisit ignoreHyps).size > 0 then
    elabVeilDestructAllHyps recursive ignoreHyps
where
  existsBinderName (whnfType : Expr) : MetaM Name := do
    match_expr whnfType with
  | Exists _ body => return body.bindingName!
  | _ => throwError "Expected an existential quantifier, got {whnfType}"
end

private inductive GenericStateKind
  | environmentState
  | backgroundTheory

def elabVeilConcretizeState : TacticM Unit := veilWithMainContext do
  let mut tacticsToExecute := #[]
  for (k, hyp) in (← getAbstractStateHyps) do
    let simpLemmaName := mkIdent $ ← mkFreshUserName stateSimpHypName
    let existingName := mkIdent $ hyp.userName
    let concreteState := mkIdent $ mkVeilImplementationDetailName existingName.getId
    let getter := match k with
    | .environmentState => mkIdent ``getFrom
    | .backgroundTheory => mkIdent ``readFrom
    let concretize ← `(tacticSeq|try (rcases (@$(mkIdent ``exists_eq') _ ($(getter) $existingName)) with ⟨$concreteState, $simpLemmaName⟩; simp only [$simpLemmaName:ident] at *; clear $existingName; veil_rename_hyp $concreteState => $existingName; clear $simpLemmaName))
    tacticsToExecute := tacticsToExecute.push concretize
  for t in tacticsToExecute do
    veilWithMainContext $ veilEvalTactic t
where
  getAbstractStateHyps : TacticM (Array (GenericStateKind × LocalDecl)) := veilWithMainContext do
    let mut abstractStateHyps := #[]
    for hyp in (← getLCtx) do
      let `(term|$x:ident) ← delabVeilExpr hyp.type
        | continue
      if x.getId == environmentStateName then
        abstractStateHyps := abstractStateHyps.push (.environmentState, hyp)
      else if x.getId == environmentTheoryName then
        abstractStateHyps := abstractStateHyps.push (.backgroundTheory, hyp)
    return abstractStateHyps

/-- Similar idea to `elabVeilConcretizeState`, but for fields when
`FieldRepresentation` is used. This also does simplification using
`LawfulFieldRepresentation` and unfolds the `fieldUpdate`s.
Note that even parts of the simplication have been done during WP
generation, it might still be necessary here since the post-condition
might contain `get` and we need to use laws to eliminate `get (set ...)`. -/
def elabVeilConcretizeFields : TacticM Unit := veilWithMainContext do
  -- TODO how to eliminate the code repetition wrt. the WP generation?
  let lctx ← getLCtx
  let some hyp := lctx.findDecl? (fun decl =>
    if decl.type.getForallBody.getAppFn.constName? == Option.some ``FieldRepresentation
    then .some decl else .none) | return
  let some lawfulRep := lctx.findDecl? (fun decl =>
    if decl.type.getForallBody.getAppFn.constName? == Option.some ``LawfulFieldRepresentation
    then .some (mkIdent decl.userName) else .none) | return
  -- get the state label type
  let .forallE _ dom _ _ := hyp.type | return
  let some labelTypeName := dom.constName? | return
  -- get the state from the hypothesis by ... some hack
  let stateTypeName := labelTypeName.getPrefix
  let some stHyp := lctx.findDecl? (fun decl =>
    if decl.type.getAppFn'.constName? == Option.some stateTypeName
    then .some decl else .none) | return
  let fields ← getFieldIdentsForStruct stateTypeName
  -- (1) do basic simplification using `LawfulFieldRepresentation`
  let mut tacs : Array (TSyntax `Lean.Parser.Tactic.tacticSeq) := #[]
  tacs := tacs.push <| ← `(tacticSeq| veil_simp only [$(mkIdent `fieldRepresentationSetSimpPre):ident])
  -- (2) simplify using `get_set_idempotent'`
  let simpTerms ← fields.mapM fun f =>
    `(($lawfulRep .$f).$(mkIdent `get_set_idempotent') (by infer_instance_for_iterated_prod))
  tacs := tacs.push <| ← `(tacticSeq| open $(mkIdent `Classical):ident in veil_simp only [$[$simpTerms:term],*] at *)
  -- (3) simplify the resulting things
  let localSimpTerms := #[fieldLabelToDomain stateName, fieldLabelToCodomain stateName]
  tacs := tacs.push <| ← `(tacticSeq| open $(mkIdent `Classical):ident in veil_simp only [$(mkIdent `fieldRepresentationSetSimpPost):ident, $[$localSimpTerms:ident],*] at *)
  -- (4) concretize the `FieldRepresentation.get`-ed fields
  let rep := mkIdent hyp.userName
  let st := mkIdent stHyp.userName
  for f in fields do
    let f : Ident := ⟨f.raw⟩
    let tmpField := mkIdent <| mkVeilImplementationDetailName f.getId
    tacs := tacs.push <| ← `(tacticSeq| generalize (($rep _).$(mkIdent `get)) $st.$f = $tmpField at * ; dsimp [$[$localSimpTerms:ident],*] at $tmpField:ident ; veil_rename_hyp $tmpField:ident => $f:ident)

  for t in tacs do
    veilWithMainContext $ veilEvalTactic t

def elabVeilSmt (stx : Syntax) (trace : Bool := false) : TacticM Unit := veilWithMainContext do
  let idents ← getPropsInContext
  let solverOptions ← `(term| [("finite-model-find", "true"), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")])
  let auto_tac ← `(tactic| smt ($(mkIdent `config):ident := {$(mkIdent `trust):ident := $(mkIdent ``true), $(mkIdent `model):ident := $(mkIdent ``true), $(mkIdent `extraSolverOptions):ident := $solverOptions}) [$[$idents:ident],*])
  if trace then
    addSuggestion stx auto_tac
  else
    veilEvalTactic auto_tac

@[inherit_doc veil_clear]
def elabVeilClearHyps (ids : Array (TSyntax `ident)) : TacticM Unit := veilWithMainContext do
  let mut toClear := ids
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    if ← isDecidableInstance decl.type then
      toClear := toClear.push (mkIdent decl.userName)
  for id in toClear do
    veilEvalTactic $ ← `(tactic| try clear $id:ident)

@[inherit_doc veil_destruct_goal]
def elabVeilDestructGoal : TacticM Unit := veilWithMainContext do
  veilEvalTactic $ ← `(tactic| repeat' constructor)

def elabVeilSimp (trace? : Bool) (o : Option Syntax) (params : Option (Array (TSyntax [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma]))) (loc : Option (TSyntax `Lean.Parser.Tactic.location)) : TacticM Unit := veilWithMainContext do
  let cfg ← `(optConfig| ($(mkIdent `failIfUnchanged):ident := $(mkIdent ``false)))
  let discharger : Option (TSyntax `Lean.Parser.Tactic.discharger) := Option.none
  let simpCall ← match trace? with
    | true => `(tactic| simp? $cfg:optConfig $[$discharger]? $[only%$o]? $[[$[$params],*]]? $[$loc]?)
    | false => `(tactic| simp $cfg:optConfig $[$discharger]? $[only%$o]? $[[$[$params],*]]? $[$loc]?)
  -- FIXME: the suggestion won't work properly for `simp?` because `evalTactic` does `withRef`
  veilEvalTactic simpCall

def elabVeilWp : TacticM Unit := veilWithMainContext do
  -- NOTE: In some cases (e.g. for `doesNotThrow`), we get internal Loom
  -- definitions like `⊤`. `loomLogicSimp` ensures these are unfolded.
  let tac ← `(tactic| veil_simp only [$(mkIdent `wpSimp):ident,  $(mkIdent `loomLogicSimp):ident])
  veilEvalTactic tac (isDesugared := false)

def elabVeilIntros : TacticM Unit := veilWithMainContext do
  let tac ← `(tactic| unhygienic intros; try intro $(mkIdent `th) $(mkIdent `st) ⟨$(mkIdent `has), $(mkIdent `hinv)⟩;)
  veilEvalTactic tac

def elabVeilFol : TacticM Unit := veilWithMainContext do
  let tac ← `(tacticSeq| (veil_simp only [$(mkIdent `substateSimp):ident, $(mkIdent `invSimp):ident, $(mkIdent `smtSimp):ident,] at *; veil_concretize_state; veil_concretize_fields; veil_destruct; veil_simp only [$(mkIdent `smtSimp):ident] at *; veil_intros))
  veilEvalTactic tac (isDesugared := false)

def elabVeilSolve : TacticM Unit := veilWithMainContext do
  let tac ← `(tactic| veil_intros; veil_wp; veil_fol; veil_smt)
  veilEvalTactic tac (isDesugared := false)

def elabVeilSplitIfs : TacticM Unit := veilWithMainContext do
  veilEvalTactic (← `(tactic| veil_simp only [$(mkIdent `ifSimp):ident] at *)) (isDesugared := false)
  veilEvalTactic $ ← `(tactic| try split_ifs)

def elabVeilFail : TacticM Unit := veilWithMainContext do
  throwError "veil_fail: failing on purpose"

def withTiming (name : String) (tac : TacticM Unit) : TacticM Unit := do
  let startTime ← IO.monoMsNow; tac; let endTime ← IO.monoMsNow
  trace[veil.debug] s!"tactic {name} took {endTime - startTime}ms"

elab_rules : tactic
  | `(tactic| veil_rename_hyp $[$xs:term => $ys:ident],*) => do withTiming "veil_rename_hyp" $ elabVeilRenameHyp xs ys
  | `(tactic| veil_destruct $ids:ident*) => do withTiming "veil_destruct" $ elabVeilDestructSpecificHyp ids
  | `(tactic| veil_clear $ids:ident*) => do withTiming "veil_clear" $ elabVeilClearHyps ids
  | `(tactic| veil_destruct_goal) => do withTiming "veil_destruct_goal" elabVeilDestructGoal
  | `(tactic| veil_concretize_state) => do withTiming "veil_concretize_state" elabVeilConcretizeState
  | `(tactic| veil_concretize_fields) => do withTiming "veil_concretize_fields" elabVeilConcretizeFields
  | `(tactic| veil_smt%$tk) => do withTiming "veil_smt" $ elabVeilSmt tk
  | `(tactic| veil_smt?%$tk) => do withTiming "veil_smt?" $ elabVeilSmt tk true
  | `(tactic| veil_simp $[only%$o]? $[[$[$params],*]]? $[$loc]?) => do withTiming "veil_simp" $ elabVeilSimp (trace? := false) o params loc
  | `(tactic| veil_simp? $[only%$o]? $[[$[$params],*]]? $[$loc]?) => do withTiming "veil_simp?" $ elabVeilSimp (trace? := true) o params loc
  | `(tactic| veil_wp) => do withTiming "veil_wp" elabVeilWp
  | `(tactic| veil_intros) => do withTiming "veil_intros" elabVeilIntros
  | `(tactic| veil_fol) => do withTiming "veil_fol" elabVeilFol
  | `(tactic| veil_solve) => do withTiming "veil_solve" elabVeilSolve
  | `(tactic| veil_split_ifs) => do withTiming "veil_split_ifs" elabVeilSplitIfs
  | `(tactic| veil_fail) => elabVeilFail

end Veil
