import Lean
import Veil.Base
import Veil.Frontend.DSL.State.SubState
import Veil.Frontend.DSL.Module.Util
import Veil.Util.Meta
import Smt
import Veil.Backend.SMT.Preprocessing
import Veil.Backend.SMT.Quantifiers
import Veil.Util.ReplacingInstances
import Veil.Util.UnhygienicCasesM

open Lean Elab Tactic Meta Simp Tactic.TryThis Parser.Tactic
namespace Veil

abbrev AccumulatedTacticKinds := [``Lean.Parser.Tactic.tacticSeq, `tactic, `tactic.seq]

/-- State for accumulating tactic syntax. Essentially an array of `tacticSeq`
or `tactic` syntaxes. -/
abbrev AccumulatedTactics := Array (TSyntax AccumulatedTacticKinds)

/-- Convert the accumulated tactic syntax to a `Format`. -/
def AccumulatedTactics.toFormat (sep : Std.Format) (s : AccumulatedTactics) : CoreM Format := do
  let tacs ← s.flatMapM fun (stx : TSyntax AccumulatedTacticKinds) => do
    match stx with
    | `(Parser.Tactic.tacticSeq| $tacs:tactic*) => return tacs.getElems
    | `(Parser.Tactic.seq1| $tacs:tactic;*) => return tacs.getElems
    | `(tactic| $tac) => return #[tac]
  let res ← tacs.mapM PrettyPrinter.ppTactic
  return Std.Format.joinSep res.toList sep

abbrev DesugarTacticM := StateRefT AccumulatedTactics TacticM

/-- `<|>` for `DesugarTacticM` that also backtracks the accumulated tactics
state. The default `Alternative` instance for `StateRefT'` does not restore
the mutable ref cell on failure, so tactics recorded by the first branch
would leak into the second. This wraps `TacticM`'s `<|>` (which properly
backtracks tactic state) with manual save/restore of the ref cell. -/
def DesugarTacticM.orElse (x : DesugarTacticM α) (y : Unit → DesugarTacticM α) : DesugarTacticM α := fun ref => do
  let saved ← ref.get
  x ref <|> (do ref.set saved; y () ref)

def DesugarTacticM.runCore (giveSuggestion? : Bool) (stx : Syntax) (x : DesugarTacticM α) : TacticM α := do
  let ref ← IO.mkRef (#[] : AccumulatedTactics)
  let showSuggestion : TacticM Unit := do
    let s ← ref.get
    -- this is an approximation to checking whether `stx` is a top-level tactic;
    -- without this, multiple suggestions would be generated for a single tactic
    -- that itself invokes other tactics internally
    let notNestedTactic := stx.getHeadInfo? matches Option.some (.original ..)
    if giveSuggestion? && !s.isEmpty && notNestedTactic then
      -- some part here is inspired by `Aesop/Util/Basic.lean`
      let fmap ← getFileMap
      let (indent, col) := stx.getRange?.elim (0, 0) (Tactic.TryThis.getIndentAndColumn fmap)
      let doIndentation? ← checkIfFullyOccupies fmap
      let sep := if doIndentation? then Std.Format.line else " ; "
      let fmt ← AccumulatedTactics.toFormat sep s
      let txt := fmt.pretty (indent := indent) (column := col)
      -- if the desugared result will not be indented across multiple lines,
      -- then just squash it into a single line
      let txt := if doIndentation? then txt else txt.removeLeadingSpaces.map fun c => if c == '\n' then ' ' else c
      Tactic.TryThis.addSuggestion (header := "After desugaring: ") stx txt
  try
    let a ← x ref  -- StateRefT is ReaderT, so we apply directly
    showSuggestion
    return a
  catch e =>
    showSuggestion  -- Show what we accumulated before the error
    throw e
where
 -- this does not have to be `TacticM`, but for tracing purposes it's easier this way
 checkIfFullyOccupies (fmap : FileMap) : TacticM Bool := do
  match stx.getRange? with
  | none =>
    -- trace[veil.debug] "no range info for tactic {stx}"
    return false
  | some r =>
    if !(r.stop + '\n') ∈ fmap.positions then
      -- trace[veil.debug] "stop position {r.stop} not in FileMap positions for tactic {stx}"
      -- trace[veil.debug] "file map positions: {fmap.positions}"
      return false
    else
      let s := fmap.source
      let some startPos := s.pos? r.start | return false
      let some startLineStartPos := startPos.revFind? '\n' | return false
      -- the substring from the start of the line where `stx` is on to the beginning of `stx`
      let some substr := s.slice? startLineStartPos startPos | return false
      -- trace[veil.debug] "substring before tactic {stx}: {substr}"
      return substr.all Char.isWhitespace

def DesugarTacticM.runByOption (stx : Syntax) (x : DesugarTacticM α) : TacticM α := do
  let giveSuggestion? := veil.desugarTactic.get (← getOptions)
  x.runCore giveSuggestion? stx

/-- A wrapper around Lean's standard `evalTactic`. ALWAYS use this instead of
`evalTactic`.

This has two purposes:
  - it uses `withoutRecover`, ensuring errors/exceptions are not silently swallowed
  - it records the evaluated tactic when `isDesugared` is `true`, which can be
    displayed for desugaring (see `DesugarTacticM.run`) -/
def veilEvalTactic (tac : TSyntax AccumulatedTacticKinds) (isDesugared : Bool := true) : DesugarTacticM Unit := do
  -- record the tactic syntax
  if isDesugared then modify fun s => s.push tac
  -- evaluate the tactic
  withoutRecover $ evalTactic tac

/-- The same as `withMainContext`, but does not just work on `TacticM`. -/
def withMainContextGeneral [Monad m] [MonadControlT MetaM m] [MonadLiftT TacticM m] (tac : m α) : m α := do
  (← getMainGoal).withContext tac

/-- Like `withMainContextGeneral`, but does nothing if there are no unsolved goals (as
opposed to throwing a "no goals to be solved" error). -/
def veilWithMainContext [Inhabited α] [Monad m] [MonadControlT MetaM m] [MonadLiftT TacticM m] (tac : m α) : m α := do
  if (← getUnsolvedGoals).length != 0 then
    withMainContextGeneral tac
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
respective fields, recursively.

Use `only [Foo, Bar]` to only destruct structures with those names. -/
syntax (name := veil_destruct) "veil_destruct" (colGt ident)* ("only" "[" ident,* "]")? ("without" "[" ident,* "]")? : tactic
/-- A different implementation of `veil_destruct` that simply collects
certain `structure`/`class` types to destruct and then pass them to `cases_type*`. -/
syntax (name := veil_destruct') "veil_destruct'" : tactic
/-- Destruct hypotheses whose type heads match the given identifiers.

Use `without [h₁, h₂]` to leave those hypotheses untouched while recursively
destructing the rest. -/
syntax (name := veil_cases_type) "veil_cases_type" ("*")? (ppSpace colGt ident)+ ("without" "[" ident,* "]")? : tactic
/-- Split the goal into sub-goals. -/
syntax (name := veil_destruct_goal) "veil_destruct_goal" : tactic

syntax (name := __veil_concretize_state_wp) "__veil_concretize_state_wp" : tactic
syntax (name := __veil_concretize_state_tr) "__veil_concretize_state_tr" : tactic
syntax (name := __veil_concretize_fields_wp) "__veil_concretize_fields_wp" ("!")? : tactic
syntax (name := __veil_concretize_fields_tr) "__veil_concretize_fields_tr" : tactic

syntax (name := veil_intros) "veil_intros" : tactic
/-- Do `intros` to bring all higher-order values (e.g., values of structures
into the local context. This is useful when such values are at the heading
`∀`s and we want to subsequently eliminate them. -/
syntax (name := veil_intro_ho) "veil_intro_ho" : tactic
syntax (name := veil_fol) "veil_fol" ("!")? : tactic
/-- Concretize abstract state and fields for WP-style goals. This includes:
1. Simplifying with `substateSimp`, `invSimp`, `smtSimp`, ``forallQuantifierSimp` (and `ghostRelSimp` if enabled)
2. Introducing higher-order values with `veil_intro_ho`
3. Small-scale axiomatization of ghost relations (if `veil.unfoldGhostRel` is false)
4. Concretizing abstract state variables with `__veil_concretize_state_wp`
5. Concretizing field representations with `__veil_concretize_fields_wp`

Use `!` for fast mode which uses `invSimp, smtSimp` only and fast field concretization. -/
syntax (name := veil_concretize_wp) "veil_concretize_wp" ("!")? : tactic
/-- Concretize abstract state and fields for transition-style goals. This includes:
1. Neutralizing decidable instances with `__veil_neutralize_decidable_inst`
2. Concretizing abstract state variables with `__veil_concretize_state_tr`
3. Concretizing field representations with `__veil_concretize_fields_tr` -/
syntax (name := veil_concretize_tr) "veil_concretize_tr" : tactic

syntax (name := veil_simp) "veil_simp" simpTraceArgsRest : tactic
syntax (name := veil_simp_trace) "veil_simp?" simpTraceArgsRest : tactic

syntax (name := veil_dsimp) "veil_dsimp" dsimpTraceArgsRest : tactic
syntax (name := veil_dsimp_trace) "veil_dsimp?" dsimpTraceArgsRest : tactic

syntax (name := veil_wp) "veil_wp" : tactic
/-- Apply the generated local-WP bridge theorem to a public WP VC.

The public goal remains
`act.meetsSpecificationIfSuccessfulAssuming assu pre post`, but this tactic
turns it into the local/core obligation used by the fast WP pipeline. It builds
the three equality proofs needed by the generated theorem:

* assumptions equal their `Assumptions.core_simplified`,
* preconditions equal either `Invariants.core_simplified` or a generated
  field-lambda returning `True` for initializer goals whose precondition is
  `fun _ _ => True`,
* the action WP equals the abstract-state RHS saved in `wp_local_eq`.

After applying the theorem, it introduces the exposed theory/state fields and
the local assumptions, so downstream tactics can assume the context already
contains `has` and `hinv` in core form. -/
syntax (name := veil_apply_local_wp) "veil_apply_local_wp" : tactic

/-- Apply the generated local-TR bridge theorem to a public TR VC.

The public goal remains
`tr.meetsSpecificationIfSuccessfulAssuming assu pre post`, but this tactic
turns it into a field-exposed obligation over the core assumptions,
core precondition, and an abstract-state transition hypothesis.  It closes the
bridge theorem's side conditions using:

* `Assumptions.core_simplified_eq`,
* `Invariants.core_simplified_eq` or a generated `True` core for initializer
  preconditions,
* the action's generated `.tr_abstract` theorem.

Unlike the WP path, the abstract transition RHS is not a separate saved
predicate definition: `.tr_abstract` rewrites from the concrete `.tr` directly
to the same `.tr` specialized to abstract theory/state. -/
syntax (name := veil_apply_local_tr) "veil_apply_local_tr" : tactic

/-- Neutralize all `Decidable` instances in the goal by replacing them
with `Classical.propDecidable`. Without this, the `Decidable` instances
in the local context might prevent `veil_concretize_state` or
`veil_concretize_fields` from abstracting states/fields in the `if` conditions.

NOTE: This is not done at the stage of WP generation since `veil_wp` uses
`simp [wpSimp]` to simplify the goal, which, at the same time, _seems_ to
replace the noncomputable `Decidable` instances with those in the local context.
Therefore, unless we do not use `simp [wpSimp]`, the changes made to `Decidable`
instances during WP generation will be reverted, and this tactic is still
required in verification. -/
syntax (name := __veil_neutralize_decidable_inst) "__veil_neutralize_decidable_inst" ("!")? (ppSpace location)? : tactic

syntax (name := __veil_ghost_relation_ssa) "__veil_ghost_relation_ssa" ("at" ident)? : tactic

syntax (name := veil_solve) "veil_solve" : tactic
/-- Add local `Nonempty α` instances for every local `Inhabited α` hypothesis. -/
syntax (name := veil_infer_nonempty) "veil_infer_nonempty" : tactic
syntax (name := veil_smt) "veil_smt" : tactic
syntax (name := veil_smt_trace) "veil_smt?" : tactic

syntax (name := veil_split_ifs) "veil_split_ifs" : tactic
syntax (name := veil_solve_wp) "veil_solve_wp" : tactic
syntax (name := __veil_solve_wplo) "__veil_solve_wplo" : tactic
syntax (name := __veil_solve_wp_conservative) "__veil_solve_wp_conservative" : tactic
syntax (name := veil_solve_wp_doesnotthrow) "veil_solve_wp_doesnotthrow" : tactic
/-- Solve transition-style goals.

This first probes the local-TR path (`veil_apply_local_tr` followed by
`__veil_solve_trlo`).  If the bridge theorem does not apply, it falls back to
the conservative route: introduce with `veil_intros`, simplify with
`invSimp`/`actSimp`/`ifSimp`, destruct conjunctions/existentials, split
conditionals, concretize the transition, and finish with `veil_fol; veil_solve`. -/
syntax (name := veil_solve_tr) "veil_solve_tr" : tactic

syntax (name := __veil_solve_trlo) "__veil_solve_trlo" : tactic
syntax (name := __veil_solve_tr_conservative) "__veil_solve_tr_conservative" : tactic

/-- Solve bounded model checking (trace) goals. This includes:
1. Introducing hypotheses with `veil_intros`
2. Destructing existentials and conjunctions
3. Simplifying with `nextSimp` and `smtSimp`
4. Calling `veil_smt` -/
syntax (name := veil_bmc) "veil_bmc" : tactic

/-- Massage the Veil goal to make it readable. Use this to begin any
interactive proof of a goal generated by Veil. -/
syntax (name := veil_unveil) "unveil" : tactic

/-- Tactic for debugging purposes. Just throws an error. -/
syntax (name := veil_fail) "veil_fail" : tactic

attribute [ifSimp] ite_true ite_false dite_true dite_false ite_self
  if_true_left if_true_right if_false_left if_false_right

@[ifSimp] theorem not_if {_ : Decidable c} :
  (¬ (if c then t else e)) = (if c then ¬ t else ¬ e) := by
  by_cases c <;> simp_all

attribute [ifSimp] Compl.compl Classical.not_forall

attribute [invSimp] RelationalTransitionSystem.assumptions
attribute [nextSimp] RelationalTransitionSystem.init RelationalTransitionSystem.tr RelationalTransitionSystem.next

-- Collected from the various `FieldRepresentation` atrributes
attribute [nextSimp] FieldRepresentation.get FieldRepresentation.set
FieldRepresentation.mkFromSingleSet instFinmapLikeAsFieldRep
IteratedArrow.curry Equiv.coe_fn_mk Function.comp IteratedProd'.equiv
IteratedProd.toIteratedProd' FieldRepresentation.setSingle
FieldRepresentation.FinmapLike.setSingle' IteratedArrow.uncurry List.foldr
IteratedProd.foldMap FieldUpdatePat.footprintRaw IteratedProd.zipWith
Option.elim List.foldl FieldUpdatePat.pad IteratedProd.default HAppend.hAppend
IteratedProd.append Eq.mp LawfulFieldRepresentationSet.set_append
List.singleton_append CanonicalField.set FieldUpdateDescr.fieldUpdate
FieldUpdatePat.match IteratedProd.patCmp Bool.and_true Bool.and_eq_true
decide_eq_true_eq ite_eq_left_iff Bool.false_eq_true false_and and_self
reduceIte ite_true ite_false and_true true_and List.head?


def elabVeilRenameHyp (xs ys : Array Syntax) : TacticM Unit := do
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

/-- Hypotheses which should be cleared on `veil_clear`. These are details of
the Veil implementation which the user should not be exposed to. -/
def hypTypesToClear : List Name := [``IsSubReaderOf, ``IsSubStateOf, ``DecidableEq,
  ``Decidable, ``FieldRepresentation, ``LawfulFieldRepresentation]

def hypNamesToClear : List Name := [environmentTheoryName,
  environmentStateName, fieldConcreteTypeName]

/-- Hypotheses which should not be sent to the SMT solver. -/
def hypTypesToIgnore : List Name := hypTypesToClear ++ [``Inhabited, ``Nonempty]

/-- Hypotheses which should not be destructed by `veil_destruct`.
Note: `Inhabited` is intentionally NOT here — we want to destruct it
so that `Inhabited` instance in the goal gets replaced by a concrete variable. -/
def hypTypesToSkipDestruct : List Name := hypTypesToClear ++ [``Nonempty]

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
        | .some sn => hypTypesToIgnore.contains sn
      let typ ← whnf hyp.type
      let isInhabitationFact := (typ.isAppOf ``Nonempty) || (typ.isAppOf ``Inhabited)
      let isProp ← Meta.isProp typ
      return isIgnored || isInhabitationFact || !isProp

private def unaryClassArg? (className : Name) (ty : Expr) : TacticM (Option Expr) := do
  let ty ← whnf ty
  match ty.getAppFn.constName?, ty.getAppArgs with
  | some name, #[arg] => return if name == className then some arg else none
  | _, _ => return none

private def hasNonemptyLocalInstance (sort : Expr) : TacticM Bool := do
  for inst in (← getLocalInstances) do
    let some sort' ← unaryClassArg? ``Nonempty (← Meta.inferType inst.fvar) | continue
    if ← Meta.isDefEq sort sort' then
      return true
  return false

def elabVeilInferNonempty : DesugarTacticM Unit := veilWithMainContext do
  for decl in (← getLCtx) do
    let some sort ← unaryClassArg? ``Inhabited decl.type | continue
    unless ← hasNonemptyLocalInstance sort do
      let fvar := mkFVar decl.fvarId
      let nonemptyType ← Meta.mkAppOptM ``Nonempty #[some sort]
      let witness ← Meta.mkAppOptM ``Inhabited.default #[some sort, some fvar]
      let proof ← Meta.mkAppOptM ``Nonempty.intro #[some sort, some witness]
      let (_, goal) ← (← getMainGoal).assertHypotheses #[
        ⟨`instNonempty, nonemptyType, proof, BinderInfo.instImplicit, .default⟩
      ]
      replaceMainGoal [goal]

/-- Untrusted SMT uses proof reconstruction, whose preprocessing/simp steps need
local `Nonempty` instances for the Veil sorts they quantify over. -/
private def mkInferNonemptyIfUntrustedTactic : TacticM (TSyntax `tactic) := do
  if veil.smt.trust.get (← getOptions) then
    `(tactic| skip)
  else
    `(tactic| veil_infer_nonempty)

@[inherit_doc veil_clear]
def elabVeilClearHyps (userToClear : Array (TSyntax `ident)) : DesugarTacticM Unit := veilWithMainContext do
  let mut veilToClear := #[]
  -- collect the Veil-specific hypotheses to clear
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    if ← shouldBeCleared decl then
      veilToClear := veilToClear.push (mkIdent decl.userName)
  -- Sort the hypotheses to clear to minimise dependencies between them.
  let fvarIds ← withMainContextGeneral <| sortFVarIds <| ← getFVarIds (userToClear ++ veilToClear)
  let toClear := fvarIds.filterMap (fun fvarId => lctx.find? fvarId) |>.map (fun decl => mkIdent decl.userName)
  for id in toClear.reverse ++ toClear.reverse do
    withMainContextGeneral do
      let .some decl := (← getLCtx).findFromUserName? id.getId | pure ()
      if !(← decl.fvarId.hasForwardDeps) then
        veilEvalTactic $ ← `(tactic| try clear $id:ident)
where
  isForbiddenHypothesis (fvarId : FVarId) : TacticM Bool := do
    let some decl := (← getLCtx).find? fvarId | pure false
    pure (hypNamesToClear.contains decl.userName)
  shouldBeCleared (decl : LocalDecl) : TacticM Bool := do
    let body : Expr := decl.type.getForallBody
    let mustClearName := hypNamesToClear.contains decl.userName
    let mustClearType := match body.getAppFn.constName? with
      | .none => false
      | .some sn => hypTypesToClear.contains sn
    if mustClearName || mustClearType then
      return true
    -- Delete hypotheses of the form `State χ`
    let isStateχ ← do match body.getAppFn.constName? with
      | .none => pure false
      | .some fn =>
        if (← resolveGlobalConst stateIdent).contains fn then
          match body.getAppArgs with
          | #[.fvar fvarId] => isForbiddenHypothesis fvarId
          | _ => pure false
        else pure false
    -- Delete hypotheses of type `ρ` or `σ`
    let ofBadType ← match body with
      | .fvar fvarId => isForbiddenHypothesis fvarId
      | _ => pure false
    return isStateχ || ofBadType

mutual

/-- Destruct a structure into its fields. If `onlyStructs` is non-empty, only destructs
structures whose type names are in the `onlyStructs` list. -/
partial def elabVeilDestructSpecificHyp (ids : Array (TSyntax `ident)) (onlyStructs : List Name := []) (excludedStructs : List Name := []) : DesugarTacticM Unit := veilWithMainContext do
  if ids.size == 0 then
    elabVeilDestructAllHyps (recursive := true) (onlyStructs := onlyStructs) (excludedStructs := excludedStructs)
  else for id in ids do
    let lctx ← getLCtx
    let name := (getNameOfIdent' id)
    let .some ld := lctx.findFromUserName? name | throwError "veil_destruct: {id} is not in the local context"
    let .some sn := ld.type.getAppFn.constName? | throwError "veil_destruct: {id} is not a constant"
    -- If `onlyStructs` is non-empty, skip structures not in the list
    if excludedStructs.contains sn || (!onlyStructs.isEmpty && !onlyStructs.contains sn) then
      continue
    let .some _sinfo := getStructureInfo? (← getEnv) sn | throwError "veil_destruct: {id} ({sn} is not a structure)"
    let newFieldNames := _sinfo.fieldNames.map (mkIdent $ Name.append name ·)
    let s ← `(rcasesPat| ⟨ $[$newFieldNames],* ⟩)
    veilEvalTactic $ ← `(tactic| unhygienic rcases $(mkIdent ld.userName):ident with $s)
    -- Simplify FieldAbstractType in new field hypotheses
    -- This handles types like `FieldAbstractType node State.Label.leader`
    let dsimpLemmas := #[fieldAbstractDispatcher, fieldLabelToDomain sn, fieldLabelToCodomain sn]
    veilEvalTactic $ ← `(tactic| try dsimp [$[$dsimpLemmas:ident],*] at $[$newFieldNames:ident]*)
    -- TODO: try to give better names to the new hypotheses if they are named clauses

/-- Destruct all structures in the context into their respective
fields, (potentially) recursively. Also destructs all existentials.
If `onlyStructs` is non-empty, only destructs structures whose type names are in the list. -/
partial def elabVeilDestructAllHyps (recursive : Bool := false) (ignoreHyps : Array LocalDecl := #[]) (onlyStructs : List Name := []) (excludedStructs : List Name := []) : DesugarTacticM Unit := veilWithMainContext do
  let mut ignoreHyps := ignoreHyps
  let hypsToVisit : (Array LocalDecl → DesugarTacticM (Array LocalDecl)) := (fun ignoreHyps => veilWithMainContext do
    return (← getLCtx).decls.toArray.filterMap fun hyp? =>
      hyp?.bind fun hyp => if !ignoreHyps.contains hyp then some hyp else none)
  for hyp in (← hypsToVisit ignoreHyps) do
    ignoreHyps := ignoreHyps.push hyp
    if hyp.isImplementationDetail then
      continue
    let structureName? ← match hyp.type.getAppFn.constName? with
    | .none => pure none
    | .some sn => if (isStructure (← getEnv) sn) then pure (some sn) else pure none
    let name := mkIdent hyp.userName
    if let some sn := structureName? then
      -- Skip if onlyStructs is non-empty and this structure is not in the list
      if !hypTypesToSkipDestruct.contains sn && !excludedStructs.contains sn && (onlyStructs.isEmpty || onlyStructs.contains sn) then
        elabVeilDestructSpecificHyp #[name]
    else
      let hypType ← Meta.whnf hyp.type
      if hypType.isAppOf ``Exists then
        let lctx ← getLCtx
        -- we want the new hypotheses to have fresh names so they're
        -- not included in the ignore list, hence we don't reuse `$name`
        let x := mkIdent $ lctx.getUnusedName (← existsBinderName hypType)
        let name' := mkIdent $ lctx.getUnusedName name.getId
        veilEvalTactic $ ← `(tactic| rcases $name:ident with ⟨$x, $name'⟩)
  -- Recursively call ourselves until the context stops changing
  if recursive && (← hypsToVisit ignoreHyps).size > 0 then
    elabVeilDestructAllHyps recursive ignoreHyps onlyStructs
where
  existsBinderName (whnfType : Expr) : MetaM Name := do
  match_expr whnfType with
  | Exists _ body => return body.bindingName!
  | _ => throwError "Expected an existential quantifier, got {whnfType}"

end

def elabVeilDestruct' : DesugarTacticM Unit := veilWithMainContext do
  let mut targets := #[]
  for hyp in (← getLCtx) do
    if hyp.isImplementationDetail then continue
    let structureName? ← match hyp.type.getAppFn'.constName? with
      | .none => pure none
      | .some sn => if isStructure (← getEnv) sn then pure (some sn) else pure none
    let some nm := structureName? | continue
    if nm ∈ hypTypesToSkipDestruct then continue
    -- Special check
    -- FIXME: This is too ad-hoc ...
    if nm == ``And then continue
    targets := targets.push nm
  let targetIdents := targets.map mkIdent
  veilEvalTactic $ ← `(tactic| (try veil_cases_type* $[$targetIdents:ident]*) ; expose_names )

private inductive GenericStateKind
  | environmentState
  | backgroundTheory

/-- Get all abstract state hypotheses (variables of type `σ` or `ρ`). -/
def getAbstractStateHyps : TacticM (Array (GenericStateKind × LocalDecl)) := veilWithMainContext do
  let mut abstractStateHyps := #[]
  for hyp in (← getLCtx) do
    let `(term|$x:ident) ← delabVeilExpr hyp.type
      | continue
    if x.getId == environmentStateName then
      abstractStateHyps := abstractStateHyps.push (.environmentState, hyp)
    else if x.getId == environmentTheoryName then
      abstractStateHyps := abstractStateHyps.push (.backgroundTheory, hyp)
  return abstractStateHyps

def concretizeStateByGeneralization : TacticM (Array (TSyntax `Lean.Parser.Tactic.tacticSeq)) := veilWithMainContext do
  let mut tacticsToExecute := #[]
  for (k, hyp) in (← getAbstractStateHyps) do
    let existingName := mkIdent hyp.userName
    let concreteState := mkIdent $ mkVeilImplementationDetailName existingName.getId
    let getter := match k with
    | .environmentState => mkIdent ``getFrom
    | .backgroundTheory => mkIdent ``readFrom
    let concretize ← `(tacticSeq|try (generalize ($(getter) $existingName) = $concreteState at * ; (try clear $existingName:ident) ; veil_rename_hyp $concreteState => $existingName))
    tacticsToExecute := tacticsToExecute.push concretize
  return tacticsToExecute

/-- Concretize abstract state variables. This uses `generalize` to replace
`getFrom st` / `readFrom th` with fresh concrete names. -/
def elabVeilConcretizeStateWp : DesugarTacticM Unit := veilWithMainContext do
  let tacticsToExecute ← concretizeStateByGeneralization
  for t in tacticsToExecute do
    veilWithMainContext $ veilEvalTactic t

/-- Concretize abstract state variables for transition goals. Compared with
`elabVeilConcretizeState`, it also handles `setIn` expressions
by rewriting with `setIn_makeExplicit` and substituting to ensure both
pre-state and post-state are available in the context (for model extraction). -/
def elabVeilConcretizeStateTr : DesugarTacticM Unit := veilWithMainContext do
  let veilDestruct ← `(tactic|veil_destruct only [$(mkIdent ``And), $(mkIdent ``Exists)])

  let classicalIdent := mkIdent `Classical
  let initialSimps := #[`substateSimp, `invSimp, `smtSimp, `forallQuantifierSimp].map Lean.mkIdent
  veilEvalTactic $ ← `(tacticSeq|open $classicalIdent:ident in veil_simp only [$[$initialSimps:ident],*] at * )

  -- Step 1: Destructuring (sometimes required to enable `subst`)
  let doubleNegTac ← `(tactic| $veilDestruct )
  veilWithMainContext $ veilEvalTactic doubleNegTac

  -- Step 2: For each abstract state hyp, try rewriting with setIn_makeExplicit and subst
  for (k, s) in (← getAbstractStateHyps) do
    -- Only apply setIn_makeExplicit to mutable state (environmentState), not to background theory
    if k matches .environmentState then
      let name := mkIdent s.userName
      let tac ← `(tacticSeq| (try rw [$(mkIdent ``IsSubStateOf.setIn_makeExplicit):ident $name] at *); $veilDestruct; (try subst $name))
      if (← getUnsolvedGoals).length != 0 then
        veilWithMainContext $ veilEvalTactic tac

  -- Step 3: Concretize remaining abstract state hyps using generalize
  -- NOTE: `subst` might have removed some of the abstract state hyps, so we need to recompute them
  elabVeilConcretizeStateWp
  veilWithMainContext $ veilEvalTactic (← `(tacticSeq|veil_simp only [$(mkIdent `substateSimp):ident, $(mkIdent `smtSimp):ident] at *; $veilDestruct))

/-- Similar idea to `elabVeilConcretizeState`, but for fields when
`FieldRepresentation` is used. This also does simplification using
`LawfulFieldRepresentation` and unfolds the `fieldUpdate`s.
Note that even parts of the simplication have been done during WP
generation, it might still be necessary here since the post-condition
might contain `get` and we need to use laws to eliminate `get (set ...)`. -/
def elabVeilConcretizeFieldsWp (fast : Bool) : DesugarTacticM Unit := veilWithMainContext do
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
  let stHyps := lctx.foldl (init := []) fun acc decl =>
    if decl.type.getAppFn'.constName? == Option.some stateTypeName
    then decl :: acc else acc
  if stHyps.isEmpty then return
  let fields ← getFieldIdentsForStruct stateTypeName
  let mut tacs : Array (TSyntax `Lean.Parser.Tactic.tacticSeq) := #[]
  let localSimpTerms := #[fieldLabelToDomain stateName, fieldLabelToCodomain stateName]
  if !fast then
    -- (1) do basic simplification using `LawfulFieldRepresentation`
    tacs := tacs.push <| ← `(tacticSeq| veil_simp only [$(mkIdent `fieldRepresentationSetSimpPre):ident])
    -- (2) simplify using `get_set_idempotent'`
    let simpTerms ← fields.mapM fun f =>
      `(($lawfulRep .$f).$(mkIdent `get_set_idempotent') (by infer_instance_for_iterated_prod))
    tacs := tacs.push <| ← `(tacticSeq| open $(mkIdent `Classical):ident in veil_simp only [$[$simpTerms:term],*] at *)
    -- (3) simplify the resulting things
    tacs := tacs.push <| ← `(tacticSeq| open $(mkIdent `Classical):ident in veil_simp only [$(mkIdent `fieldRepresentationSetSimpPost):ident, $[$localSimpTerms:ident],*] at *)
  -- (4) concretize the `FieldRepresentation.get`-ed fields
  let rep := mkIdent hyp.userName
  for stHyp in stHyps do
    let st := mkIdent stHyp.userName
    for f in fields do
      let f : Ident := f
      let fDestructed := mkIdent <| Name.append st.getId f.getId -- Name.mkSimple s!"{st.getId}_{f.getId}"
      let tmpField := mkIdent <| mkVeilImplementationDetailName f.getId
      tacs := tacs.push <| ← `(tacticSeq| generalize (($rep _).$(mkIdent `get)) $st.$f = $tmpField at * ; dsimp [$[$localSimpTerms:ident],*] at $tmpField:ident ; veil_rename_hyp $tmpField:ident => $fDestructed:ident)
    -- Clear the original state hypothesis
    tacs := tacs.push <| ← `(tacticSeq| try clear $st:ident)
  for t in tacs do
    veilWithMainContext $ veilEvalTactic t

/-- Similar to `elabVeilConcretizeFields`, but for transition goals where
hypotheses have the form `st'.field = FieldRepresentation.set [...] st.field`
or `st'.field = st.field` (for unchanged fields).
This first applies `congrArg (χ_rep _).get` to view the equalities through
the field representation, then calls `elabVeilConcretizeFields`, and finally
simplifies with `smtSimp`. -/
def elabVeilConcretizeFieldsTr : DesugarTacticM Unit := veilWithMainContext do
  -- The label type is `State.Label`, resolve it to fully qualified name
  let labelTypeName ← resolveGlobalConstNoOverloadCore (structureFieldLabelTypeName stateName)

  let lctx ← getLCtx
  -- Find the χ fvar (field concrete type) in the local context
  let some χFvarId := (lctx.findFromUserName? fieldConcreteTypeName).map LocalDecl.fvarId | return

  -- Step 1: Identify hypotheses where the equality's type involves a field label.
  -- These are equalities like:
  -- ```lean4
  -- hleader' : st'.leader = Veil.FieldRepresentation.set [((some n, ()), fun x => true)] st.leader
  -- hpending' : st'.pending = st.pending  -- unchanged field
  -- ```
  -- The equality type will be `χ State.Label.leader` or similar.
  let mut hypsToTransform : Array Ident := #[]

  for decl in lctx do
    if decl.isImplementationDetail then continue
    -- Check if the type is an equality
    let some (eqType, _, _) := decl.type.eq? | continue
    -- Check if the equality type is `χ Label.field` (e.g., `χ State.Label.leader`)
    if eqType.getAppFn'.fvarId? != some χFvarId then continue
    let some fieldLabelName := eqType.getAppArgs'[0]?.bind (·.constName?) | continue
    if labelTypeName.isPrefixOf fieldLabelName && fieldLabelName != labelTypeName then
      hypsToTransform := hypsToTransform.push (mkIdent decl.userName)

  -- Apply `congrArg (χ_rep _).get` to each identified hypothesis
  -- to "view" the equality through the field representation
  for hyp in hypsToTransform do
    let tac ← `(tactic| apply $(mkIdent ``congrArg) ($(fieldRepresentation) _).$(mkIdent `get) at $hyp:ident)
    veilEvalTactic tac

  -- Step 2: Concretize fields using the standard procedure
  elabVeilConcretizeFieldsWp false

  -- Step 3: Final simplification
  -- NOTE: `Bool.eq_decide_to_iff` is ONLY used here for now; it might be
  -- added into `smtSimp` as well, but just to be very conservative
  veilWithMainContext $ veilEvalTactic (← `(tactic| veil_simp only [$(mkIdent `substateSimp):ident, $(mkIdent `smtSimp):ident,
    $(mkIdent ``Bool.eq_decide_to_iff):ident] at *))

@[inherit_doc __veil_neutralize_decidable_inst]
def elabVeilNeutralizeDecidableInst (deep : Bool) (loc : Option (TSyntax ``Lean.Parser.Tactic.location)) : DesugarTacticM Unit := veilWithMainContext do
  let nm := if deep then ``Veil.Util.neutralizeDecidableInstGeneral else ``Veil.Util.neutralizeDecidableInstDepth0
  veilEvalTactic $ ← `(tactic| veil_simp only [$(mkIdent nm):ident] $[$loc]?)
  clearDecidableInsts
where
  clearDecidableInsts : DesugarTacticM Unit := veilWithMainContext do
    let mut toClear := #[]
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      if decl.type.getForallBody.getAppFn'.isConstOf ``Decidable then
        toClear := toClear.push (mkIdent decl.userName)
    for id in toClear do
      veilEvalTactic $ ← `(tactic| try clear $id:ident)

private def smallScaleAxiomatizationSimpSet (withLocalRPropTC? : Bool) : Array Name :=
  let base := #[``id, ``instIsSubStateOfRefl, ``instIsSubReaderOfRefl]
  if withLocalRPropTC? then
    base.push ``Veil.replaceLocalRPropWithCoreAppOnLCtxFields |>.push `LocalRProp.core
  else base.push `ghostRelSimp

/-- Perform "small-scale axiomatization" for a ghost relation `nmFull` based
on its application `target`. Returns the local `let`-declaration for the
ghost relation (with only its specific arguments being abstracted over),
the local `have`-declaration for the equality lemma, and the number of
specific arguments. -/
private def smallScaleAxiomatization (nBaseParams nExtraParams : Nat) (nm nmFull : Name) (target : Expr) (withLocalRPropTC? : Bool) : TacticM (Option (Expr × Expr × Nat)) := veilWithMainContext do
  -- Note that this is currently done in a very hacky way, might need better
  -- support on the segmentation of parameters. It could be possible to
  -- generalize this logic of "abstracting over specific arguments that appear
  -- in certain positions only".

  -- step 1: abstract over the first application of `nmFull`
  let args := target.getAppArgs'
  let baseArgs := args.take nBaseParams
  let suffixArgs := args.drop (args.size - nExtraParams - 2)  -- 2: for theory and state
  let nm' ← mkFreshBinderNameForTactic <| nm.appendAfter "_axiomatized"
  -- heavily exploit the arguments structure
  let body ← do
    let preBody := mkAppN target.getAppFn' baseArgs
    let ty ← inferType preBody
    forallBoundedTelescope ty (args.size - nExtraParams - 2 - nBaseParams) fun newVarExprs _ => do
      let preBody2 := mkAppN preBody (newVarExprs ++ suffixArgs)
      -- FIXME: if `extraParams` depend on arguments replaced by `newVarExprs`, this might not work
      mkLambdaFVars newVarExprs preBody2
  let bodyTy ← inferType body
  -- create the `let` binding, simulating `let nm' : bodyTy := body`
  let mv ← getMainGoal
  mv.withContext do
  let (fv, mv') ← mv.let nm' body bodyTy
  let grfv := Expr.fvar fv    -- the local `let`-declaration
  replaceMainGoal [mv']
  let mv := mv'
  mv.withContext do

  -- step 2: instantiate the equation lemma
  let some eqs ← getEqnsFor? nmFull
    -- | throwError "unexpected error: could not find equation lemmas for {nmFull}"
    | return none
  let some eq := eqs[0]?    -- the first one should be enough
    -- | throwError "unexpected error: no equation lemmas for {nmFull}"
    | return none
  let (newEq, proof) ← forallTelescope bodyTy fun xs _ => do
    let eqApplied ← mkAppOptM eq ((baseArgs ++ xs ++ suffixArgs) |>.map Option.some)
    let eqAppliedTy ← inferType eqApplied
    let eqAppliedTy ← instantiateMVars eqAppliedTy
    let some (_, _, newEqRHS) := eqAppliedTy.eq?
      | throwError "unexpected error: equation lemma for {nmFull} does not have equality type: got {eqAppliedTy}"
    let newEqLHS := mkAppN grfv xs
    let newEq ← mkEq newEqLHS newEqRHS
    let newEq ← mkForallFVars xs newEq
    let proof ← mkLambdaFVars xs eqApplied
    pure (newEq, proof)

  -- step 3: do some simplification (this makes this code a bit too specific, but anyway)
  -- for now, only do `dsimp` here
  let newEq' ← (Simp.dsimp <| smallScaleAxiomatizationSimpSet withLocalRPropTC?) newEq
  -- create the `have` binding
  let eqName ← mkFreshBinderNameForTactic (nm'.appendAfter "_eq")
  -- simulating `have eqName : newEq := proof`; not sure why there is no direct API for this?
  let (fv, mv') ← mv.let eqName proof newEq'.expr
  let mv'' ← mv'.clearValue fv
  let eqfv := Expr.fvar fv
  replaceMainGoal [mv'']

  pure (some (grfv, eqfv, args.size - nExtraParams - 2 - nBaseParams))

/-- For every ghost relation in `derivedDefns` that is used in `e`, this tactic
first tries creating a local `let`-declaration for it with only its own specific
arguments being the arguments. For example, a ghost relation `foo` can appear in `e`
in the form of a full application `foo (base parameters) a b (theory) (state) (extra params)`,
where `(theory)` and `(state)` are _ground_ terms (e.g., `Theory` and `State`
elements for the current module), then the local declaration will be
`foo' := fun a b => foo (base parameters) a b (theory) (state) (extra params)`.

Then this tactic tries using the equation lemma of `foo` to introduce an equality
`∀ a b, foo' a b = <rhs>` into the local context, where `rhs` is the right-hand side
of the equation lemma, after proper argument instantiation and simplification.

This tactic returns a `HashMap` from each involved ghost relation's full name
to its corresponding local `let`-declaration (as an `Expr`, essentially a fvar)
and the number of its specific arguments. -/
private def ghostRelationSSACore (derivedDefns : Std.HashMap Name DerivedDefinition) (nBaseParams : Nat) (e : Expr) (withLocalRPropTC? : Bool) : TacticM (Std.HashMap Name (Expr × Nat)) := veilWithMainContext do
  let nms := e.getUsedConstantsAsSet
  let mut info : Array (Name × Expr × Nat) := #[]
  for (nm, dd) in derivedDefns do
    unless dd.kind matches .ghost true do
      continue
    -- maybe the full name should be stored as metadata
    let nmFull ← resolveGlobalConstNoOverloadCore nm
    unless nms.contains nmFull do
      continue
    let nExtraParams := dd.extraParams.size
    let some target := findValidFullApplication nmFull nExtraParams e
      | continue
    if let some (grfv, _, nn) ← smallScaleAxiomatization nBaseParams nExtraParams nm nmFull target withLocalRPropTC? then
      info := info.push (nmFull, grfv, nn)
  return Std.HashMap.ofList info.toList
where
  findValidFullApplication (nmFull : Name) (nExtraParams : Nat) (e : Expr) := e.findExt? fun e' => Id.run do
    unless e'.getAppFn'.constName? == some nmFull do
      return .visit
    -- do a very simple checking that the theory and state must be ground
    let args := e'.getAppRevArgs'.drop nExtraParams
    unless args.size ≥ nBaseParams + 2 do
      return .done
    if args[0]!.hasLooseBVars || args[1]!.hasLooseBVars then
      return .done
    return .found

/-- Small-scale axiomatization for ghost relations. Its first part is
done in `ghostRelationSSACore` (please refer to its docstring for details).
The second part is to "fold back" the usages of ghost relations into
their local `let`-declarations, and finally clear the bodies of these
local declarations to complete the axiomatization.

Currently, it is only performed over one hypothesis or the main target,
depending on whether `hyp` is provided. -/
def ghostRelationSSA (mod : Module) (hyp : Option Name) : TacticM Unit := veilWithMainContext do
  let (baseParams, _) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition (.ghost true) (Std.HashSet.emptyWithCapacity 0))
  let ty ← match hyp with
    | .some hname => do
      let ldecl ← getLocalDeclFromUserName hname
      pure ldecl.type
    | .none => getMainTarget''
  let info ← ghostRelationSSACore mod._derivedDefinitions baseParams.size ty mod._useLocalRPropTC
  veilWithMainContext do
  let ty' ← foldingByDefEq baseParams.size info ty
  let mv ← getMainGoal
  match hyp with
  | some hname => do
    let ldecl ← getLocalDeclFromUserName hname
    -- NOTE: Since `hyp` is above the newly introduced `let`-declarations,
    -- we need to change the order.
    let mv' ← mv.replaceLocalDeclDefEq ldecl.fvarId ty'  -- or `changeLocalDecl`?
    let (_, mv'') ← mv'.withReverted #[ldecl.fvarId] fun mvv fvars => mvv.withContext do
      -- finally, clear the bodies of the local `let`-declarations
      let fvs := info.fold (init := []) fun acc _ (grfv, _) => grfv :: acc
      let mvv' ← clearValues mvv fvs
      pure ((), fvars.map Option.some, mvv')
    replaceMainGoal [mv'']
  | none => do
    let mv' ← mv.change ty'
    -- finally, clear the bodies of the local `let`-declarations
    let fvs := info.fold (init := []) fun acc _ (grfv, _) => grfv :: acc
    let mv'' ← clearValues mv' fvs
    replaceMainGoal [mv'']
where
  /-- Fold back the usages of ghost relations based on definitional equality. -/
  foldingByDefEq (nBaseParams : Nat) (info : Std.HashMap Name (Expr × Nat)) (target : Expr) : MetaM Expr :=
    Meta.transform target (skipConstInApp := true)
      (pre := fun e' => do
        let some nm := e'.getAppFn'.constName? | return .continue
        let some (grfv, nSpecificArgs) := info[nm]? | return .continue
        let args := e'.getAppArgs'
        let specificArgs := args.drop nBaseParams |>.take nSpecificArgs
        -- check if we can replace `e'` with `grfv specificArgs`
        let target := mkAppN grfv specificArgs
        if ← isDefEq e' target then
          trace[veil.debug] "folding {e'} to {target}"
          return .done target
        return .done e'
      )
  clearValues (mv : MVarId) (fvs : List Expr) : MetaM MVarId :=
    match fvs with
    | [] => return mv
    | fv :: fvs' => do
      let mv' ← mv.clearValue fv.fvarId!
      clearValues mv' fvs'

def elabGhostRelationSSA (hyp : Option Ident) : DesugarTacticM Unit := veilWithMainContext do
  let mod ← getCurrentModule
  ghostRelationSSA mod <| hyp.map (·.getId)
  -- do some simplification for the goal
  let simps := smallScaleAxiomatizationSimpSet mod._useLocalRPropTC |>.map Lean.mkIdent
  withMainContextGeneral do
  veilEvalTactic $ ← `(tactic| expose_names ; veil_dsimp only [$[$simps:ident],*])

private def mkVeilSmtTactic : TacticM (TSyntax `tactic) := do
  let idents ← getPropsInContext
  let opts ← getOptions
  let fmfEnabled := veil.smt.finiteModelFind.get opts
  let timeout := veil.smt.timeout.get opts
  let trustEnabled := veil.smt.trust.get opts
  let fmfValue := if fmfEnabled then "true" else "false"
  let trustValue := mkIdent <| if trustEnabled then ``true else ``false
  let trustValueNegated := mkIdent <| if trustEnabled then ``false else ``true
  let solverOptions ← `(term| [("finite-model-find", $(Syntax.mkStrLit fmfValue)), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")])
  let smtTac ← `(tactic| smt ($(mkIdent `config):ident := {$(mkIdent `trust):ident := $trustValue:ident, $(mkIdent `embedBool):ident := $trustValueNegated:ident, $(mkIdent `model):ident := $(mkIdent ``true), $(mkIdent `timeout):ident := $(mkIdent ``Option.some) $(quote timeout), $(mkIdent `extraSolverOptions):ident := $solverOptions}) [$[$idents:ident],*])
  if trustEnabled then
    return ← `(tactic| open $(mkIdent `Classical):ident in $smtTac:tactic)
  else
    return ← `(tactic| (veil_infer_nonempty; open $(mkIdent `Classical):ident in $smtTac:tactic))

def elabVeilSolve : DesugarTacticM Unit := veilWithMainContext do
  let solver := veil.solver.get (← getOptions)
  let tac ← match solver with
    | .smt => `(tactic| veil_smt)
    | .grind => `(tactic| grind)
    | .grindAndSMT => `(tactic| first | grind | veil_smt)
    | .custom => `(tactic| fail "Custom solver is not specified")
  veilEvalTactic tac

def elabVeilSmt (stx : Syntax) (trace : Bool := false) : DesugarTacticM Unit := veilWithMainContext do
  -- It's necessary to `open Classical` to make proof reconstruction work.
  -- Otherwise, sometimes it fails due to failing to infer `Decidable` instances.
  let auto_tac ← mkVeilSmtTactic
  if trace then
    addSuggestion stx auto_tac
  else
    veilEvalTactic auto_tac

@[inherit_doc veil_destruct_goal]
def elabVeilDestructGoal : DesugarTacticM Unit := veilWithMainContext do
  veilEvalTactic $ ← `(tactic| repeat' constructor)

private def disableFailIfUnchangedInSimpConfig (cfg : TSyntax ``Lean.Parser.Tactic.optConfig) : CoreM (TSyntax ``Lean.Parser.Tactic.optConfig) := do
  match cfg with
  | `(optConfig| $[$cfgItems:configItem]* ) =>
    `(optConfig| ($(mkIdent `failIfUnchanged):ident := $(mkIdent ``false)) $[$cfgItems:configItem]* )
  | _ => `(optConfig| ($(mkIdent `failIfUnchanged):ident := $(mkIdent ``false)) )

def elabVeilSimp (trace? : Bool) (cfg : TSyntax ``Lean.Parser.Tactic.optConfig) (o : Option Syntax) (params : Option (Array (TSyntax [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma]))) (loc : Option (TSyntax `Lean.Parser.Tactic.location)) : DesugarTacticM Unit := veilWithMainContext do
  let cfg ← disableFailIfUnchangedInSimpConfig cfg
  let discharger : Option (TSyntax `Lean.Parser.Tactic.discharger) := Option.none
  let simpCall ← match trace? with
    | true => `(tactic| simp? $cfg:optConfig $[$discharger]? $[only%$o]? $[[$[$params],*]]? $[$loc]?)
    | false => `(tactic| simp $cfg:optConfig $[$discharger]? $[only%$o]? $[[$[$params],*]]? $[$loc]?)
  -- FIXME: the suggestion won't work properly for `simp?` because `evalTactic` does `withRef`
  veilEvalTactic simpCall

def elabVeilDSimp (trace? : Bool) (cfg : TSyntax ``Lean.Parser.Tactic.optConfig) (o : Option Syntax) (params : Option (Array (TSyntax [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma]))) (loc : Option (TSyntax `Lean.Parser.Tactic.location)) : DesugarTacticM Unit := veilWithMainContext do
  let cfg ← disableFailIfUnchangedInSimpConfig cfg
  let simpCall ← match trace? with
    | true => `(tactic| dsimp? $cfg:optConfig $[only%$o]? $[[$[$params],*]]? $[$loc]?)
    | false => `(tactic| dsimp $cfg:optConfig $[only%$o]? $[[$[$params],*]]? $[$loc]?)
  -- FIXME: the same issue as above?
  veilEvalTactic simpCall

attribute [loomLogicSimpForVeil ↓] topE topPureE

def elabVeilWp : DesugarTacticM Unit := veilWithMainContext do
  -- NOTE: In some cases (e.g. for `doesNotThrow`), we get internal Loom
  -- definitions like `⊤`. `loomLogicSimp` ensures these are unfolded.
  let tac ← `(tactic| open $(mkIdent `Classical):ident in veil_simp only [$(mkIdent `wpSimp):ident, $(mkIdent `loomLogicSimpForVeil):ident])
  veilEvalTactic tac

private def mkLocalPreconditionTactics (mod : Module) (theoryType stateType pre : Expr)
    (tacticName : String) : DesugarTacticM (Option (TSyntax `tactic) × TSyntax `tactic) := do
  let invariantsEqName ← resolveGlobalConstNoOverloadCore <| toCoreSimplifiedEqName assembledInvariantsName
  let invariantsName ← resolveGlobalConstNoOverloadCore assembledInvariantsName
  let truePre ← withLocalDeclsDND
      #[(mkVeilImplementationDetailName `th, theoryType), (mkVeilImplementationDetailName `st, stateType)]
      fun xs => mkLambdaFVars xs (mkConst ``True)
  if pre.getAppFn'.isConstOf invariantsName then
    -- For ordinary action VCs, let `Invariants.core_simplified_eq` determine
    -- the still-open `preCore` metavariable.  Closing `preCore` first with bare
    -- `Invariants.core_simplified` loses the module-prefix arguments because
    -- the expected type is already just the field-core function type.
    pure (none, ← `(tactic| exact $(mkIdent invariantsEqName):ident))
  else if ← isDefEq pre truePre then
    -- Initializer VCs have precondition `fun _ _ => True`.  Build the matching
    -- field-level core directly instead of asking Lean to infer a shared
    -- definition's module/typeclass prefix while bridge theorem arguments are
    -- still metavariables.
    let hole ← `(Lean.Parser.Term.funBinder| _ )
    let fieldBinders := Array.replicate (mod.immutableComponents.size + mod.mutableComponents.size) hole
    let truePreCore ← mkFunSyntax fieldBinders <| mkIdent ``True
    pure (some (← `(tactic| exact $truePreCore:term)), ← `(tactic| exact fun _ _ => $(mkIdent ``rfl)))
  else
    throwError "{tacticName}: expected precondition to be Invariants or True, got{indentExpr pre}"

/-- Implementation of `veil_apply_local_wp`; see the tactic syntax declaration
for the user-facing behavior. -/
def elabVeilApplyLocalWp : DesugarTacticM Unit := veilWithMainContext do
  -- First expose explicit action parameters; after this, the goal should have
  -- the public `meetsSpecificationIfSuccessfulAssuming` shape.
  veilEvalTactic $ ← `(tactic| unhygienic intros)
  -- For performance, use `refine` on the generated bridge theorem and only
  -- provide the small side-condition terms.  The large VC pieces
  -- (`act/assu/pre/post`) are implicit theorem arguments and are recovered from
  -- the expected target instead of being rebuilt as one giant application.
  let mod ← getCurrentModule
  let goal ← getMainGoal
  let localThmApp ← goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let target := target.consumeMData
    -- After introducing action parameters, the goal should be exactly the
    -- public VC shape.  Keep the original `assu/pre/post`; the tactic only
    -- changes how this goal is proved.
    let (theoryType, stateType, act, pre) ←
      match_expr target with
      | VeilM.meetsSpecificationIfSuccessfulAssuming _ theoryType stateType _ act _ pre _ =>
        pure (theoryType, stateType, act, pre)
      | _ =>
        throwError "veil_apply_local_wp: expected a VeilM.meetsSpecificationIfSuccessfulAssuming goal, got{indentExpr target}"
    let some actName := act.getAppFn'.constName?
      | throwError "veil_apply_local_wp: expected action to be headed by a constant, got{indentExpr act}"
    let wpLocalEqName ← resolveGlobalConstNoOverloadCore (toWpLocalEqName actName)
    let (preCoreTac?, hPreTac) ← mkLocalPreconditionTactics mod theoryType stateType pre "veil_apply_local_wp"
    pure (wpLocalEqName, preCoreTac?, hPreTac)
  let (wpLocalEqName, preCoreTac?, hPreTac) := localThmApp
  -- NOTE: We intentionally use a lightly-applied `refine` here rather than
  -- building a fully-instantiated theorem application.  On larger modules,
  -- constructing the complete application forces Lean to elaborate huge VC
  -- terms all at once and can blow up memory.
  --
  -- The bracketed `<;> [...]` block documents the fixed side-goal order
  -- produced by the bridge theorem and keeps tactic desugaring readable.  The
  -- implicit `pred` argument is left as a natural goal.  Do not solve it
  -- directly: the `hWp` branch rewrites by `wp_local_eq`, and that unification
  -- determines `pred` to be the action's abstract WP.  The initial goals are:
  -- `pred`, `assuCore`, `preCore`, `hAssu`, `hPre`, `hWp`, and `hLocal`.
  let preCoreTac ← match preCoreTac? with
    | some tac => pure tac
    | none => `(tactic| skip)
  let hWpTac ←
    `(tactic|
      (unhygienic intro $(mkIdent `handler) $(mkIdent `th) $(mkIdent `st);
       rw [$(mkIdent wpLocalEqName):ident]))
  veilEvalTactic $ ← `(tactic|
    refine' $localMeetsSpecificationIfSuccessfulAssuming:ident ?_ ?_ ?_ ?_ ?_ ?_ <;>
      [ skip
      ; skip
      ; $preCoreTac:tactic
      ; exact $(mkIdent <| toCoreSimplifiedEqName assembledAssumptionsName):ident
      ; $hPreTac:tactic
      ; $hWpTac:tactic
      ; skip ])
  let [_] ← getUnsolvedGoals
    | throwError "veil_apply_local_wp: expected exactly one local/core goal after applying the bridge theorem"
  -- The remaining goal is the theorem's `hLocal` premise.  Introduce exposed
  -- fields with the same user-name shape that the counterexample printer
  -- recognizes (`th.field`/`st.field`), even though these are now plain local
  -- fields rather than projections.  The final two hypotheses keep the usual
  -- names expected by the local WP solver.
  let introNames :=
    (mod.immutableComponents.map (fun sc => Name.append `th sc.name)) ++
    (mod.mutableComponents.map (fun sc => Name.append `st sc.name)) ++
    #[`has, `hinv]
  let introIdents := introNames.map Lean.mkIdent
  veilEvalTactic $ ← `(tactic| unhygienic intro $introIdents*)
  -- Finally, do some cleanup; now this is somehow like `unveil`
  -- NOTE: `whnf` for unfolding `.wp_local_eq.pred`
  let has := mkIdent `has ; let hinv := mkIdent `hinv
  let tac ← `(tacticSeq|
    __veil_neutralize_decidable_inst
    whnf
    try unfold $(mkIdent <| toCoreSimplifiedName assembledAssumptionsName):ident at $has:ident
    try unfold $(mkIdent <| toCoreSimplifiedName assembledInvariantsName):ident at $hinv:ident
    veil_dsimp only [$(mkIdent `nextSimp):ident]
    veil_dsimp only [↓ $(mkIdent `reduceStateLabelDomainCodomainDsimproc):ident]
    )
  veilEvalTactic tac

/-- Implementation of `veil_apply_local_tr`; see the tactic syntax declaration
for the user-facing behavior. -/
def elabVeilApplyLocalTr : DesugarTacticM Unit := veilWithMainContext do
  -- Match `veil_apply_local_wp`: first expose explicit action parameters so the
  -- remaining target is the public TR VC.
  veilEvalTactic $ ← `(tactic| unhygienic intros)
  let mod ← getCurrentModule
  let goal ← getMainGoal
  let localInfo ← goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let target := target.consumeMData
    let (theoryType, stateType, tr, pre) ←
      match_expr target with
      | Transition.meetsSpecificationIfSuccessfulAssuming theoryType stateType tr _ pre _ =>
        pure (theoryType, stateType, tr, pre)
      | _ =>
        throwError "veil_apply_local_tr: expected a Transition.meetsSpecificationIfSuccessfulAssuming goal, got{indentExpr target}"
    let some trName := tr.getAppFn'.constName?
      | throwError "veil_apply_local_tr: expected transition to be headed by a constant, got{indentExpr tr}"
    let trAbstractName ← resolveTransitionAbstractName trName
    let (preCoreTac?, hPreTac) ← mkLocalPreconditionTactics mod theoryType stateType pre "veil_apply_local_tr"
    pure (trAbstractName, preCoreTac?, hPreTac)
  let (trAbstractName, preCoreTac?, hPreTac) := localInfo
  -- The theorem shape mirrors the WP bridge theorem.  The bracketed
  -- `<;> [...]` block exposes the fixed side-goal order in the generated
  -- tactic script.  The implicit `trAbs` argument is deliberately left open;
  -- the `hTr` branch closes it by applying `.tr_abstract`, whose target is the
  -- transition specialized to abstract theory/state.  The resulting goals are:
  -- `trAbs`, `assuCore`, `preCore`, `hAssu`, `hPre`, `hTr`, and `hLocal`.
  let preCoreTac ← match preCoreTac? with
    | some tac => pure tac
    | none => `(tactic| skip)
  let hTrTac ← `(tactic| (unhygienic intro _ _ _; apply $(mkIdent trAbstractName):ident))
  veilEvalTactic $ ← `(tactic|
    refine' $localTransitionMeetsSpecificationIfSuccessfulAssuming:ident ?_ ?_ ?_ ?_ ?_ ?_ <;>
      [ skip
      ; skip
      ; $preCoreTac:tactic
      ; exact $(mkIdent <| toCoreSimplifiedEqName assembledAssumptionsName):ident
      ; $hPreTac:tactic
      ; $hTrTac:tactic
      ; skip ])
  let [_] ← getUnsolvedGoals
    | throwError "veil_apply_local_tr: expected exactly one local/core goal after applying the bridge theorem"
  -- The remaining local obligation exposes theory fields, pre-state fields,
  -- post-state fields, then `has`, `hinv`, and the abstract transition fact.
  -- Keep names close to the old concretization convention for counterexample
  -- display and for downstream local tactics.
  let introNames :=
    (mod.immutableComponents.map (fun sc => Name.append `th sc.name)) ++
    (mod.mutableComponents.map (fun sc => Name.append `st sc.name)) ++
    -- FIXME: Use better name than `s₁`
    (mod.mutableComponents.map (fun sc => Name.append `s₁ sc.name)) ++
    #[`has, `hinv, `htr]
  let introIdents := introNames.map Lean.mkIdent
  veilEvalTactic $ ← `(tactic| unhygienic intro $introIdents*)
  let has := mkIdent `has ; let hinv := mkIdent `hinv ; let htr := mkIdent `htr
  let tac ← `(tacticSeq|
    whnf at $htr:ident
    try unfold $(mkIdent <| toCoreSimplifiedName assembledAssumptionsName):ident at $has:ident
    try unfold $(mkIdent <| toCoreSimplifiedName assembledInvariantsName):ident at $hinv:ident
    veil_dsimp only [$(mkIdent `nextSimp):ident] at $htr:ident ⊢
    )
  veilEvalTactic tac
where
  -- FIXME: This is wacky
  resolveTransitionAbstractName (trName : Name) : TacticM Name := do
    let base? :=
      match trName with
      | .str p "tr" => some p
      | _ => none
    let some base := base?
      | throwError "veil_apply_local_tr: expected transition constant ending in `.tr`, got {trName}"
    resolveGlobalConstNoOverloadCore (toTransitionAbstractName base)

def elabVeilIntros : DesugarTacticM Unit := veilWithMainContext do
  let wpIntro ← `(tactic|intro $(mkIdent `th) $(mkIdent `st) ⟨$(mkIdent `has), $(mkIdent `hinv)⟩)
  -- This is a bit annoying, but we name these `s₀` and `s₁` rather than `st`
  -- and `st'`. This ensures `concretize_state` generates `st` and `st'`.
  let trIntro ← `(tactic|intro $(mkIdent `th) $(mkIdent `st) $(mkIdent `s₁) ⟨$(mkIdent `has), $(mkIdent `hinv)⟩)
  let tac ← `(tactic| unhygienic intros; (try first | $wpIntro:tactic | $trIntro:tactic ); (try unhygienic intros))
  veilEvalTactic tac

-- NOTE: For now, this is effectively `introv` (but not exactly, since
-- `introv` does not skip over mdata); if the goal is properly HO-lifted,
-- then this should bring all higher-order values into the local context.
-- We can change this later if we want more sophisticated behavior.
partial def elabVeilIntroHO : TacticM Unit := veilWithMainContext do
  introsDep
where
  introsDep : TacticM Unit := do
    let t ← getMainTarget
    let t := t.consumeMData
    match t with
    | Expr.forallE _ _ e _ =>
      if e.hasLooseBVars then
        liftMetaTactic fun goal ↦ do
          let (_, goal) ← goal.intro1P
          pure [goal]
        introsDep
    | _ => pure ()

/-- Shared tactic sequence: simplify with
initial simp sets, introduce HO values, and handle ghost relations. Used by
both `elabVeilConcretizeWp` and `elabVeilSolveWplo`. -/
private def elabSimplifyBeforeConcretizeWp [Monad m] [MonadOptions m] [MonadQuotation m] (fast simpHinv : Bool) : m (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  let classicalIdent := mkIdent `Classical
  let unfoldghostRel? := veil.unfoldGhostRel.get (← getOptions)
  let initialSimps := if fast
    then #[`invSimp, `smtSimp]
    else #[`substateSimp, `invSimp, `smtSimp, `forallQuantifierSimp]
  let initialSimps := if unfoldghostRel? then initialSimps.push `ghostRelSimp else initialSimps
  let initialSimps := initialSimps.map Lean.mkIdent
  let ghostRelTac ← if unfoldghostRel?
    then `(tactic| skip )
    -- NOTE: Both here and below assume the hypothesis for `Invariants` has name `hinv`
    else `(tactic| (__veil_ghost_relation_ssa at $(mkIdent `hinv):ident ; __veil_ghost_relation_ssa ))
  let simpTac ← if simpHinv
    then `(tactic| open $classicalIdent:ident in veil_simp only [$[$initialSimps:ident],*] at *)
    else -- skip `hinv`
      `(tactic| open $classicalIdent:ident in veil_simp only [$[$initialSimps:ident],*] at $(mkIdent `has):ident ⊢ )
  `(tacticSeq| $simpTac ; veil_intro_ho ; $ghostRelTac )

@[inherit_doc veil_concretize_wp]
def elabVeilConcretizeWp (fast : Bool) : DesugarTacticM Unit := veilWithMainContext do
  let preTac ← elabSimplifyBeforeConcretizeWp fast true
  let inferNonemptyTac ← mkInferNonemptyIfUntrustedTactic
  let concretizeFieldsTac ← if fast
    then `(tactic| __veil_concretize_fields_wp !)
    else `(tactic| __veil_concretize_fields_wp)
  let tac ← `(tacticSeq| $inferNonemptyTac:tactic; ($preTac) ; __veil_neutralize_decidable_inst at * ; __veil_concretize_state_wp ; $concretizeFieldsTac )
  veilEvalTactic tac

@[inherit_doc veil_concretize_tr]
def elabVeilConcretizeTr : DesugarTacticM Unit := veilWithMainContext do
  -- FIXME: figure out how to do the axiomatisation for ghost relations in TR
  let ghostRel ← `(tactic| veil_simp only [$(mkIdent `ghostRelSimp):ident] at *)
  let tac ← `(tacticSeq| __veil_neutralize_decidable_inst at * ; $ghostRel; __veil_concretize_state_tr; __veil_concretize_fields_tr)
  veilEvalTactic tac

def elabVeilFol (fast : Bool) : DesugarTacticM Unit := veilWithMainContext do
  let tac ← do
    let classicalIdent := mkIdent `Classical
    let inferNonemptyTac ← mkInferNonemptyIfUntrustedTactic
    let tac ← if fast
      then `(tactic| (veil_destruct' ; veil_dsimp only at *; veil_intros) )
      else `(tactic| (veil_destruct; (open $classicalIdent:ident in veil_simp only [$(mkIdent `smtSimp):ident] at * ); veil_intros) )
    -- FIXME: There is `inferNonemptyTac` both in `veil_fol` and `veil_smt` and `concretize_wp`. Just keep one?
    `(tactic| ($inferNonemptyTac:tactic; $tac:tactic))
  veilEvalTactic tac

def elabVeilHuman : DesugarTacticM Unit := veilWithMainContext do
  veilEvalTactic $ ← `(tactic| veil_intros; veil_wp; __veil_neutralize_decidable_inst at *; veil_concretize_wp; veil_clear; veil_simp at *)

/-- The fast WP-local continuation after `veil_apply_local_wp` has succeeded.

At this point the goal is already the field-exposed local/core obligation, so
this path deliberately avoids the old concretization steps. -/
def elabVeilSolveWplo : DesugarTacticM Unit := veilWithMainContext do
  let tac ← `(tacticSeq|
    open $(mkIdent `Classical):ident in veil_simp only [$(mkIdent `smtSimp):ident]
    veil_intro_ho
    veil_fol !
    veil_solve
    )
  veilEvalTactic tac

def elabVeilSolveTrlo : DesugarTacticM Unit := veilWithMainContext do
  -- When we want to resort to SMT solver, we might have to do some destruction
  -- to avoid higher-order quantification
  let solver := veil.solver.get (← getOptions)
  let solveTac ← match solver with
    -- FIXME: `veil_destruct' ; (unhygienic intros)` is like a wachy `veil_fol !`,
    -- but somehow we need to avoid `subst` here, otherwise the counterexample
    -- printing might miss some substituted variables
    | .smt | .grindAndSMT => `(tactic| (repeat' (first | veil_cases_type* $(mkIdent ``Exists) $(mkIdent ``And) without [$(mkIdent `hinv)] | split_ifs at *)) <;> (expose_names ; veil_destruct' ; (unhygienic intros) ; veil_solve) )
    | _ => `(tactic| (veil_destruct' ; veil_solve) )
  -- NOTE: For `tr` case, usually `smtSimp` will call `State.ext_iff`
  -- and this will incur `@Eq (FieldAbstractType ...)` which can make
  -- `veil_smt` fail. So we do the dsimproc after `smtSimp`.
  let htr := mkIdent `htr
  let tac ← `(tacticSeq|
    open $(mkIdent `Classical):ident in veil_simp only [$(mkIdent `smtSimp):ident] at $htr:ident
    veil_dsimp only [↓ $(mkIdent `reduceStateLabelDomainCodomainDsimproc):ident] at $htr:ident
    __veil_neutralize_decidable_inst at $htr:ident ⊢
    $solveTac
    )
  veilEvalTactic tac

/-- The conservative WP solver (the original approach without wp_local_eq). -/
def elabVeilSolveWpConservative : DesugarTacticM Unit := veilWithMainContext do
  let tac ← `(tactic| veil_wp; veil_concretize_wp; veil_fol; veil_solve)
  veilEvalTactic tac

def elabVeilSolveWpDoesNotThrow : DesugarTacticM Unit := veilWithMainContext do
  -- If you don't write `assert`, then most likely the goal is trivial
  veilEvalTactic <| ← `(tactic| veil_intros; veil_wp )
  veilWithMainContext do
    let simpleSolveTac ← `(tactic| veil_simp only
      [↓ $(mkIdent ``ite_self):ident, ↓ $(mkIdent ``implies_true):ident])
    veilEvalTactic <| ← `(tactic| solve | $simpleSolveTac:tactic | veil_concretize_wp; veil_fol; veil_solve)

/-- Try the local-WP path first; if applying the local bridge theorem fails,
fall back to the conservative solver.

The probe is `veil_apply_local_wp` itself.  On success it has already changed
the goal into the exposed local/core obligation, so we commit to
`__veil_solve_wplo`.  On failure, backtracking restores the original public VC
and the old conservative route starts with `veil_intros` as before. -/
def elabVeilSolveWp : DesugarTacticM Unit := veilWithMainContext do
  let probeSucceeds? ← DesugarTacticM.orElse
    (do
      veilWithMainContext <| veilEvalTactic <| ← `(tactic| veil_apply_local_wp)
      pure true)
    (fun _ => pure false)
  if probeSucceeds? then
    veilWithMainContext <| veilEvalTactic <| ← `(tactic| __veil_solve_wplo)
  else
    veilWithMainContext <| veilEvalTactic <| ← `(tactic| veil_intros; __veil_solve_wp_conservative)

/-- The conservative TR solver: the original transition route after
`veil_intros`, without trying the local TR bridge theorem. -/
def elabVeilSolveTrConservative : DesugarTacticM Unit := veilWithMainContext do
  -- NOTE: `veil_fol !` seems to sometimes remove variables from the context
  -- if they're not used. This is undesirable when the variable is an action
  -- parameter, because we need to keep it in the context for model extraction.
  let tac ← `(tactic| veil_simp only [$(mkIdent `invSimp):ident, $(mkIdent `actSimp):ident] at *; veil_simp only [$(mkIdent `ifSimp):ident] at *; veil_destruct only [$(mkIdent ``Exists), $(mkIdent ``And)]; veil_split_ifs ; all_goals (veil_concretize_tr; veil_fol ; veil_solve))
  veilEvalTactic tac

/-- Try the local-TR path first; if applying the local bridge theorem fails,
fall back to the old transition solver.

The probe mirrors `veil_solve_wp`: `veil_apply_local_tr` either commits the
goal to the exposed local/core TR obligation, or backtracking restores the
public TR VC before the conservative route starts with `veil_intros`. -/
def elabVeilSolveTr : DesugarTacticM Unit := veilWithMainContext do
  let probeSucceeds? ← DesugarTacticM.orElse
    (do
      veilWithMainContext <| veilEvalTactic <| ← `(tactic| veil_apply_local_tr)
      pure true)
    (fun _ => pure false)
  if probeSucceeds? then
    veilWithMainContext <| veilEvalTactic <| ← `(tactic| __veil_solve_trlo)
  else
    veilWithMainContext <| veilEvalTactic <| ← `(tactic| veil_intros; __veil_solve_tr_conservative)

@[inherit_doc veil_bmc]
def elabVeilBmc : DesugarTacticM Unit := veilWithMainContext do
  -- FIXME: sometimes we still have abstract dispatchers in the types, so as a
  -- hack, we just dsimp them here
  let dsimpLemmas := #[mkIdent ``Inhabited.default, fieldAbstractDispatcher, fieldLabelToDomain stateName, fieldLabelToCodomain stateName]
  let dsimpTac←  `(tactic| try dsimp [$[$dsimpLemmas:ident],*])
  let inferNonemptyTac ← mkInferNonemptyIfUntrustedTactic
  let tac ← `(tacticSeq| $inferNonemptyTac:tactic; veil_simp only [$(mkIdent `nextSimp):ident]; veil_simp only [↓ $(mkIdent ``existsQuantifierSimpGuarded):ident]; veil_intros; $inferNonemptyTac:tactic; veil_destruct; $dsimpTac; veil_simp only [$(mkIdent `smtSimp):ident]; $dsimpTac; veil_smt)
  veilEvalTactic tac

def elabVeilSplitIfs : DesugarTacticM Unit := veilWithMainContext do
  veilEvalTactic $ ← `(tactic| try split_ifs at *)
  veilEvalTactic $ ← `(tactic| all_goals expose_names )

def elabVeilFail : TacticM Unit := veilWithMainContext do
  throwError "veil_fail: failing on purpose"

-- Implementation-detail tactics (prefixed with __) should be handled first,
-- followed by user-facing tactics
@[
  -- Implementation-detail tactics
  tactic __veil_concretize_state_wp,
  tactic __veil_concretize_state_tr,
  tactic __veil_concretize_fields_wp,
  tactic __veil_concretize_fields_tr,
  tactic __veil_neutralize_decidable_inst,
  tactic __veil_ghost_relation_ssa,
  tactic __veil_solve_wplo,
  tactic __veil_solve_trlo,
  tactic __veil_solve_wp_conservative,
  tactic __veil_solve_tr_conservative,
  -- User-facing tactics
  tactic veil_solve,
  tactic veil_infer_nonempty,
  tactic veil_rename_hyp,
  tactic veil_destruct,
  tactic veil_destruct',
  tactic veil_cases_type,
  tactic veil_clear,
  tactic veil_destruct_goal,
  tactic veil_smt,
  tactic veil_smt_trace,
  tactic veil_simp,
  tactic veil_simp_trace,
  tactic veil_dsimp,
  tactic veil_dsimp_trace,
  tactic veil_wp,
  tactic veil_apply_local_wp,
  tactic veil_apply_local_tr,
  tactic veil_intros,
  tactic veil_intro_ho,
  tactic veil_concretize_wp,
  tactic veil_concretize_tr,
  tactic veil_fol,
  tactic veil_solve_wp,
  tactic veil_solve_wp_doesnotthrow,
  tactic veil_solve_tr,
  tactic veil_bmc,
  tactic veil_split_ifs,
  tactic veil_unveil,
  tactic veil_fail]
def elabVeilTactics : Tactic := fun stx => do
  let res : DesugarTacticM Unit :=
  match stx with
  -- Implementation-detail tactics
  | `(tactic| __veil_concretize_state_wp) => do
    withTraceNode `veil.perf.tactic (fun _ => return "__veil_concretize_state_wp") elabVeilConcretizeStateWp
  | `(tactic| __veil_concretize_state_tr) => do
    withTraceNode `veil.perf.tactic (fun _ => return "__veil_concretize_state_tr") elabVeilConcretizeStateTr
  | `(tactic| __veil_concretize_fields_wp $[!%$agg]?) => do
    withTraceNode `veil.perf.tactic (fun _ => return "__veil_concretize_fields_wp") (elabVeilConcretizeFieldsWp (agg.isSome))
  | `(tactic| __veil_concretize_fields_tr) => do
    withTraceNode `veil.perf.tactic (fun _ => return "__veil_concretize_fields_tr") elabVeilConcretizeFieldsTr
  | `(tactic| __veil_neutralize_decidable_inst $[!%$agg]? $[$loc]?) => do
    withTraceNode `veil.perf.tactic (fun _ => return "__veil_neutralize_decidable_inst") (elabVeilNeutralizeDecidableInst (agg.isSome) loc)
  | `(tactic| __veil_ghost_relation_ssa $[at $hyp:ident]?) => do
    withTraceNode `veil.perf.tactic (fun _ => return "__veil_ghost_relation_ssa") (elabGhostRelationSSA hyp)
  -- User-facing tactics
  | `(tactic| veil_rename_hyp $[$xs:term => $ys:ident],*) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_rename_hyp") $ elabVeilRenameHyp xs ys
  | `(tactic| veil_destruct $ids:ident* $[only [$onlyIds:ident,*]]? $[without [$excludedIds:ident,*]]?) => do
    let onlyStructs := match onlyIds with
      | some ids => ids.getElems.toList.map (fun id => id.getId)
      | none => []
    let excludedStructs := match excludedIds with
      | some ids => ids.getElems.toList.map (fun id => id.getId)
      | none => []
    withTraceNode `veil.perf.tactic (fun _ => return "veil_destruct") $ elabVeilDestructSpecificHyp ids onlyStructs excludedStructs
  | `(tactic| veil_destruct' ) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_destruct'") $ elabVeilDestruct'
  | `(tactic| veil_cases_type $[*%$recursive?]? $heads:ident* $[without [$skipIds:ident,*]]?) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_cases_type") $
      Veil.Util.elabCasesType heads (recursive := recursive?.isSome) (allowSplit := true)
        (skipNames := skipIds.elim #[] (fun ids => ids.getElems.map (·.getId)))
  | `(tactic| veil_clear $ids:ident*) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_clear") $ elabVeilClearHyps ids
  | `(tactic| veil_destruct_goal) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_destruct_goal") elabVeilDestructGoal
  | `(tactic| veil_solve) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_solve") elabVeilSolve
  | `(tactic| veil_infer_nonempty) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_infer_nonempty") elabVeilInferNonempty
  | `(tactic| veil_smt%$tk) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_smt") $ elabVeilSmt tk
  | `(tactic| veil_smt?%$tk) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_smt?") $ elabVeilSmt tk true
  | `(tactic| veil_simp $cfg:optConfig $[only%$o]? $[[$[$params],*]]? $[$loc]?) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_simp") $ elabVeilSimp (trace? := false) cfg o params loc
  | `(tactic| veil_simp? $cfg:optConfig $[only%$o]? $[[$[$params],*]]? $[$loc]?) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_simp?") $ elabVeilSimp (trace? := true) cfg o params loc
  | `(tactic| veil_dsimp $cfg:optConfig $[only%$o]? $[[$[$params],*]]? $[$loc]?) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_dsimp") $ elabVeilDSimp (trace? := false) cfg o params loc
  | `(tactic| veil_dsimp? $cfg:optConfig $[only%$o]? $[[$[$params],*]]? $[$loc]?) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_dsimp?") $ elabVeilDSimp (trace? := true) cfg o params loc
  | `(tactic| veil_wp) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_wp") elabVeilWp
  | `(tactic| veil_apply_local_wp) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_apply_local_wp") elabVeilApplyLocalWp
  | `(tactic| veil_apply_local_tr) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_apply_local_tr") elabVeilApplyLocalTr
  | `(tactic| veil_intros) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_intros") elabVeilIntros
  | `(tactic| veil_intro_ho) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_intro_ho") elabVeilIntroHO
  | `(tactic| veil_concretize_wp $[!%$agg]?) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_concretize_wp") (elabVeilConcretizeWp (agg.isSome))
  | `(tactic| veil_concretize_tr) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_concretize_tr") elabVeilConcretizeTr
  | `(tactic| veil_fol $[!%$agg]?) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_fol") (elabVeilFol (agg.isSome))
  | `(tactic| veil_solve_wp) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_solve_wp") elabVeilSolveWp
  | `(tactic| __veil_solve_wplo) => do
    withTraceNode `veil.perf.tactic (fun _ => return "__veil_solve_wplo") elabVeilSolveWplo
  | `(tactic| __veil_solve_trlo) => do
    withTraceNode `veil.perf.tactic (fun _ => return "__veil_solve_trlo") elabVeilSolveTrlo
  | `(tactic| __veil_solve_wp_conservative) => do
    withTraceNode `veil.perf.tactic (fun _ => return "__veil_solve_wp_conservative") elabVeilSolveWpConservative
  | `(tactic| __veil_solve_tr_conservative) => do
    withTraceNode `veil.perf.tactic (fun _ => return "__veil_solve_tr_conservative") elabVeilSolveTrConservative
  | `(tactic| veil_solve_wp_doesnotthrow) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_solve_wp_doesnotthrow") elabVeilSolveWpDoesNotThrow
  | `(tactic| veil_solve_tr) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_solve_tr") elabVeilSolveTr
  | `(tactic| veil_bmc) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_bmc") elabVeilBmc
  | `(tactic| veil_split_ifs) => do
    withTraceNode `veil.perf.tactic (fun _ => return "veil_split_ifs") elabVeilSplitIfs
  | `(tactic| unveil) => do
    withTraceNode `veil.perf.tactic (fun _ => return "unveil") elabVeilHuman
  | `(tactic| veil_fail) => elabVeilFail
  | _ => throwUnsupportedSyntax
  res.runByOption stx

end Veil
