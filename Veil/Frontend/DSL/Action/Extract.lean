import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Module.Names
import Veil.Core.Tools.ModelChecker.ExecutionOutcome
import Veil.Frontend.DSL.Action.Semantics.WP

open Lean Elab Command Term Meta Lean.Parser

namespace Veil.Extract

syntax injectBindersStx := "injection_begin" bracketedBinder* "injection_end"

namespace Preprocessing

attribute [dsimpFieldRepresentationGet ↓] FieldRepresentation.get FieldRepresentation.mkFromSingleSet
  instFinsetLikeAsFieldRep instFinmapLikeAsFieldRep IteratedArrow.curry
  Equiv.coe_fn_mk Function.comp IteratedProd'.equiv IteratedProd.toIteratedProd'
attribute [dsimpFieldRepresentationSet ↓] FieldRepresentation.setSingle FieldRepresentation.mkFromSingleSet
  instFinsetLikeAsFieldRep instFinmapLikeAsFieldRep FieldRepresentation.FinsetLike.setSingle' FieldRepresentation.FinmapLike.setSingle'
  IteratedArrow.curry IteratedProd'.equiv Equiv.coe_fn_mk IteratedProd.toIteratedProd' IteratedArrow.uncurry List.foldr
  IteratedProd.foldMap FieldUpdatePat.footprintRaw IteratedProd.zipWith Option.elim List.foldl

-- ad-hoc subprocedure for finding the target `State.Label.toDomain/toCodomain`
private def getLocalDSimpTargets (a b : Expr) : Array Name := Id.run do
  let mut res := #[]
  if let some nm := a.getAppFn.constName? then res := res.push nm
  if let some nm := b.getAppFn.constName? then res := res.push nm
  pure res

dsimproc_decl simpFieldRepresentationGet (Veil.FieldRepresentation.get _) := fun e => do
  let_expr FieldRepresentation.get a b c inst d := e | return .done e
  let inst' ← whnfI inst
  trace[veil.debug] m!"[{decl_name%}]: {e}, with inst = {inst'}"
  let e' := mkAppN (mkConst ``FieldRepresentation.get) #[a, b, c, inst', d]
  let res ← Veil.Simp.dsimp (#[`dsimpFieldRepresentationGet] ++ getLocalDSimpTargets a b) {} e'
  return .done res.expr

dsimproc_decl simpFieldRepresentationSetSingle (Veil.FieldRepresentation.setSingle _ _ _) := fun e => do
  let_expr FieldRepresentation.setSingle a b c inst fa v fc := e | return .done e
  let inst' ← whnfI inst
  trace[veil.debug] m!"[{decl_name%}]: {e} with inst = {inst'}"
  let e' := mkAppN (mkConst ``FieldRepresentation.setSingle) #[a, b, c, inst', fa, v, fc]
  let res ← Veil.Simp.dsimp (#[`dsimpFieldRepresentationSet] ++ getLocalDSimpTargets a b) {} e'
  return .done res.expr

end Preprocessing

/-
NOTE: The following approach for generating specialized versions of
actions and their extracted counterparts is __based on syntax manipulation__.
Therefore, it is inherently hacky and fragile.

If the specialization is done by "injecting elaboration gadgets" (e.g.,
`delta$`, `veil_dsimp%`), then it must be done in a separate `def`.
Currently, it is done where each `act.ext` appears in the syntax
(i.e., the same timing as when `NextAct` is defined).

A difficulty here is the substitution of the specialized variables
(e.g., `χ`, `χ_rep`, `χ_rep_lawful`) at the syntax level. The current
solution is to insert `letI` for them before they are used.

Further checks:
- It might be more principled and simpler (?) to do this at the `Expr` level.
- Since doing simplification that preserves the definitional equality
  is already tricky, we might as well do some more aggressive simplifications
  that requires a non-trivial proof of equality.

-/

section Specialization

variable [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [MonadOptions m] [AddMessageContext m]
  (baseParams extraParams : Array Parameter)
  (injectedBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
  (finalBody : Term)

def buildingTermWithInjectionAndParameterSpecialized
  (specializedTo : Parameter → Option Term) : m Term := do
  let baseSegments := segmentingParameters baseParams
  let extraSegments := segmentingParameters extraParams
  let body ← do
    let part1 ← mkFunctionWithSegments extraSegments finalBody
    let part2 ← `(remove_unused_binders% $injectedBinders* => $part1)
    mkFunctionWithSegments baseSegments part2
  pure body
where
 segmentingParameters (params : Array Parameter) : Array (Sum (Array Parameter) (Parameter × Term)) := Id.run do
  let mut res : Array (Sum (Array Parameter) (Parameter × Term)) := #[]
  let mut tmpArr : Array Parameter := #[]
  for p in params do
    match specializedTo p with
    | some t =>
      if !tmpArr.isEmpty then
        res := res.push (Sum.inl tmpArr)
        tmpArr := #[]
      res := res.push (Sum.inr (p, t))
    | none =>
      tmpArr := tmpArr.push p
  if !tmpArr.isEmpty then
    res := res.push (Sum.inl tmpArr)
  return res
 mkFunctionWithSegments (segments : Array (Sum (Array Parameter) (Parameter × Term))) (body : Term) : m Term := do
  segments.foldrM (init := body) fun seg curBody => do
    match seg with
    | Sum.inl params =>
      let binders ← params.mapM fun (a : Parameter) => a.binder >>= bracketedBinderToFunBinder
      mkFunSyntax binders curBody
    | Sum.inr (p, t) =>
      `(letI $(mkIdent p.name) : $p.type := $t
        $curBody)

def buildingTermWithχSpecialized
  (χ χ_rep χ_rep_lawful : Term)
  (specializedToOther : Parameter → Option Term := fun _ => none) : m Term := do
  -- HACK: `χ` depends on `injectedBinders`, so split `baseParams` accordingly.
  -- There seems no better way to do so
  let idx := baseParams.findIdx fun p => p.kind == .fieldConcreteType
  buildingTermWithInjectionAndParameterSpecialized (baseParams.take idx)
    (baseParams.drop idx ++ extraParams)
    injectedBinders finalBody fun p =>
    match p.kind with
    | .fieldConcreteType => some χ
    | .moduleTypeclass .fieldRepresentation => some χ_rep
    | .moduleTypeclass .lawfulFieldRepresentation => some χ_rep_lawful
    | _ => specializedToOther p

def buildingTermWithDefaultχSpecialized (mod : Module)
  (specializedToOther : Parameter → Option Term := fun _ => none) : m Term := do
  buildingTermWithχSpecialized baseParams extraParams injectedBinders finalBody
    (← `(($fieldConcreteDispatcher $(← mod.sortIdents)*)))
    (← `($instFieldRepresentation $(← mod.sortIdents)*))
    (← `($instLawfulFieldRepresentation $(← mod.sortIdents)*))
    specializedToOther

end Specialization

-- Ideally, we should not require this, but the `DefEq` check during
-- typeclass resolution seems to really have difficulty without this.
-- NOTE: This simplification still seems incomplete (it doesn't perform
-- certain beta-reductions), but `DefEq` checking seems to work fine with this,
-- as long as `simpFieldRepresentationGet` and `simpFieldRepresentationSetSingle`
-- are applied.
open Tactic in
/-- Simplify the types of `Decidable` instance arguments in the local context. -/
scoped elab "veil_dsimp_decidable_instances_before_extraction" : tactic => withMainContext do
  let mut targets : Array Ident := #[]
  let lctx ← getLCtx
  for ldecl in lctx do
    let ltype := ldecl.type
    if ltype.getForallBody.isAppOfArity ``Decidable 1 then
      targets := targets.push (mkIdent ldecl.userName)
  let simps := #[``Preprocessing.simpFieldRepresentationSetSingle, ``Preprocessing.simpFieldRepresentationGet].map Lean.mkIdent
  evalTactic <| ← `(tactic| dsimp -$(mkIdent `failIfUnchanged) only [$[$simps:ident],*] at $targets:ident* )

section Extraction

variable [Monad m] [MonadQuotation m] [MonadError m]
  (injectedBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (extraDsimpsForSpecialize : TSyntaxArray `ident)
  (κ : TSyntax `term) (useWeak intoMonadicActions : Bool)

def specializeAndExtractCore
  (actName : Name) (allParams : Array Parameter)
  (useFieldRepTC : Bool) : m Term := do
  -- Fully applied such that this term should have type `VeilM ..`
  let fullyAppliedAction ← buildFullyAppliedAction actName allParams
  let actionBody ← simplifyActionAfterSpecialization fullyAppliedAction
  buildExtractBody actionBody fullyAppliedAction
where
 buildFullyAppliedAction (actName : Name) (allParams : Array Parameter) : m Term := do
  -- CHECK There are some issues with assigning typeclass instance arguments
  -- using names; also, typeclass synthesis fails if we do not provide the instance
  -- in the local context explicitly, which is weird
  /-
  let allNamedArgs ← allParams.mapM fun x => do
    let arg ← x.arg
    `(Lean.Parser.Term.namedArgument| ($(mkIdent x.name) := $arg:term))
  let head := Lean.mkIdent actName
  let body : Term := ⟨mkNode `Lean.Parser.Term.app #[head, mkNullNode allNamedArgs]⟩
  pure body
  -/
  let allArgs ← allParams.mapM (·.arg)
  `(@$(mkIdent actName) $allArgs*)
 simplifyActionAfterSpecialization (fullyAppliedAction : Term) : m Term := do
  if useFieldRepTC then
    let extraDsimpsForSpecialize := extraDsimpsForSpecialize.push <| Lean.mkIdent ``id
    `(veil_dsimp% -$(mkIdent `zeta) -$(mkIdent `failIfUnchanged)
      [$(mkIdent ``Preprocessing.simpFieldRepresentationSetSingle),
      $(mkIdent ``Preprocessing.simpFieldRepresentationGet),
      $(mkIdent `Veil.VeilM.returnUnit),
      $[$extraDsimpsForSpecialize:ident],*]
      (delta% $fullyAppliedAction))
  else pure fullyAppliedAction
 buildExtractBody (body bodyBeforeSimp : Term) : m Term := do
  let multiExecMonadType ← `(term| $(mkIdent ``VeilMultiExecM) ($κ) ExId $environmentTheory $environmentState)
  let extractor := mkIdent <| (if useWeak then ``MultiExtractor.NonDetT.extractPartialList else ``MultiExtractor.NonDetT.extractList)
  -- HACK: when not `intoMonadicActions`, `targetType` is actually partial
  let targetType ← if intoMonadicActions then `($multiExecMonadType _)
    else
      let tmp ← if useWeak
        then `(term| $(mkIdent ``MultiExtractor.findOfPartialCandidates) _)
        else `(term| $(mkIdent ``MultiExtractor.findOfCandidates) _)
      `(term| $(mkIdent ``MultiExtractor.ConstrainedExtractResult) ($κ) _ ($multiExecMonadType) ($tmp))
  let extractSimps : Array Ident :=
    #[`multiExtractSimp, ``instMonadLiftT,
      -- NOTE: The following are added to work around a bug (?) fixed in Lean v4.27.0-rc1
      ``id, ``inferInstance, ``inferInstanceAs, instFieldRepresentationName].map Lean.mkIdent
  let extractSimps := if intoMonadicActions then extractSimps.push extractor else extractSimps
  let extractedBody ← if intoMonadicActions then `(($extractor ($κ) _ _ ($body) : $targetType))
    -- Use the first `show` to have more concise type information that can be
    -- registered to the discrimination tree
    else `(show $targetType ($bodyBeforeSimp) from show $targetType ($body) by extract_list_tactic)
  `((veil_dsimp% -$(mkIdent `zeta) -$(mkIdent `failIfUnchanged) [$[$extractSimps:ident],*]
    ($extractedBody)))

def specializeAndExtractSingle (mod : Module) (pi : ProcedureInfo) (extractedName : Name := toExtractedName pi.name)
  (attrs : Array (TSyntax ``Lean.Parser.Term.attrInstance) := #[]) : CommandElabM Unit := do
  let (baseParams, extraParams, actualParams) ← mod.declarationSplitParams pi.name (.procedure pi)
  let extractBody ← specializeAndExtractCore extraDsimpsForSpecialize κ useWeak intoMonadicActions pi.name (baseParams ++ extraParams ++ actualParams) mod._useFieldRepTC
  let extractBody ← `(by veil_dsimp_decidable_instances_before_extraction; exact $extractBody)
  let defBody ← buildingTermWithDefaultχSpecialized baseParams (extraParams ++ actualParams) injectedBinders extractBody mod
  let cmd ← if attrs.isEmpty
    then `(command| def $(mkIdent extractedName):ident := $defBody:term)
    else `(command| @[$[$attrs],*] def $(mkIdent extractedName):ident := $defBody:term)
  elabVeilCommand cmd

-- NOTE: We only add `multiextracted` and `multiExtractSimp` attributes to
-- procedures. Ideally, we also need to add them to the internal mode
-- actions, but actions are not usually called in the internal mode,
-- and extracting them would double the time spent in extraction.

def specializeAndExtractInitializer (mod : Module) : CommandElabM Unit := do
  specializeAndExtractSingle injectedBinders extraDsimpsForSpecialize κ useWeak true mod ProcedureInfo.initializer (toExtName initializerName |> toExtractedName)

def specializeAndExtractInternalMode (mod : Module) : CommandElabM Unit := do
  let procs := mod.procedures.filter fun p => match p.info with | .procedure _ => true | _ => false
  for ps in procs do
    let attr1 ← `(Parser.Term.attrInstance| $(mkIdent `multiextracted):ident )
    let attr2 ← `(Parser.Term.attrInstance| multiExtractSimp ↓)
    specializeAndExtractSingle injectedBinders extraDsimpsForSpecialize κ useWeak false mod ps.info (attrs := #[attr1, attr2])

def specializeAndExtractActions (mod : Module) : CommandElabM Unit := do
  let lIdent := mkIdent `l
  let labelT ← mod.labelTypeStx
  let alts ← mod.actions.mapM fun a => do
    let pi := a.info
    let (baseParams, extraParams, actualParams) ← mod.declarationSplitParams pi.name (.procedure pi)
    let extractBody ← specializeAndExtractCore extraDsimpsForSpecialize κ useWeak true (toExtName pi.name) (baseParams ++ extraParams ++ actualParams) mod._useFieldRepTC
    let args ← actualParams.mapM (·.arg)
    mkFunSyntax args extractBody
  let finalBody ← do
    let multiExecType ← `(term| $(mkIdent ``VeilMultiExecM) ($κ) ExId $environmentTheory $environmentState $(mkIdent ``Unit))
    -- Need this annotation to avoid the `failed to elaborate eliminator, expected type is not available` error
    `(fun ($lIdent : $labelT) => (($lIdent.$(mkIdent `casesOn) $alts*) : $multiExecType))
  let finalBody ← `(by veil_dsimp_decidable_instances_before_extraction; exact $finalBody)
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .actionLike actionNames)
  let defBody ← buildingTermWithDefaultχSpecialized baseParams extraParams injectedBinders finalBody mod
  let extractedName := toExtractedName assembledNextActName
  elabVeilCommand <| ←  `(command| def $(mkIdent extractedName):ident := $defBody:term)

def specializeAndExtract : CommandElabM Unit := do
  let mod ← getCurrentModule
  specializeAndExtractInitializer injectedBinders extraDsimpsForSpecialize κ useWeak mod
  specializeAndExtractInternalMode injectedBinders extraDsimpsForSpecialize κ useWeak mod
  specializeAndExtractActions injectedBinders extraDsimpsForSpecialize κ useWeak mod

syntax (name := specializeAndExtractCmdStx) "#extract" ("!")? "log_entry_being" term
  ("dsimp_with " "[" ident,* "]")? (injectBindersStx)? : command

elab_rules : command
  | `(#extract $[!%$notUseWeakSign]? log_entry_being $logelem:term $[dsimp_with [$[$extraDsimps:ident],*]]? $[injection_begin $injectedBinders:bracketedBinder* injection_end]?) => do
    let extraDsimps := extraDsimps.getD #[]
    let injectedBinders := injectedBinders.getD #[]
    specializeAndExtract injectedBinders extraDsimps logelem notUseWeakSign.isNone

private def bindersToInjectForExecution [Monad m] [MonadQuotation m] [AddMessageContext m] [MonadOptions m] [MonadTrace m] [MonadError m] [MonadEnv m] (mod : Veil.Module) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let repConfigs ← resolveConcreteRepConfigs mod._concreteRepConfig
  let binders ← mod.assumeInstArgsWithConcreteRepConfig mod.mutableComponents repConfigs
    ConcreteRepConfig.domainLawfulFieldRepInstances ConcreteRepConfig.codomainLawfulFieldRepInstances
    #[``Repr, ``Enumeration] #[``Inhabited, ``DecidableEq] false
  return binders

def runGenExtractCommand (mod : Veil.Module) : CommandElabM Unit := do
  let binders ← bindersToInjectForExecution mod
  let execListCmd ← `(command |
    attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet] $instEnumerationForIteratedProd in
    #extract! log_entry_being $(mkIdent ``Std.Format)
    injection_begin
      $[$binders]*
    injection_end)
  elabVeilCommand execListCmd

end Extraction

section VeilSpecificExtractionUtils

open MultiExtractor

instance (priority := high) {α : Type u} {p : α → Prop} [Veil.Enumeration α] [DecidablePred p] : MultiExtractor.Candidates p where
  find := fun _ => Veil.Enumeration.allValues |>.filter p
  find_iff := by simp ; grind

instance (priority := high + 100) {α : Type u} {p : α → Prop} [inst : Veil.Enumeration {a : α // p a }] : MultiExtractor.Candidates p where
  find := fun _ => inst.allValues.unattach
  find_iff := by simp ; grind

instance (priority := high + 200) {α : Type u} [Veil.Enumeration α] : MultiExtractor.Candidates (fun (_ : α) => True) where
  find := fun _ => Veil.Enumeration.allValues
  find_iff := by simp ; grind

def ConstrainedExtractResult.pickSuchThat_VeilM (p : τ → Prop) [∀ x, Decidable (p x)] [instec : ExtCandidates Candidates Std.Format p] :
  ConstrainedExtractResult Std.Format (VeilExecM m ρ σ) (VeilMultiExecM Std.Format ExId ρ σ)
  (findOfCandidates _) (VeilM.pickSuchThat τ p) := ConstrainedExtractResult.pickList _ _ _ _ p (instec := instec)

def ConstrainedExtractResult.assume_VeilM {m ρ σ} (p : Prop) [decp : Decidable p] :
  ConstrainedExtractResult Std.Format (VeilExecM m ρ σ) (VeilMultiExecM Std.Format ExId ρ σ)
  (findOfCandidates _) (@VeilM.assume m ρ σ p decp) := ConstrainedExtractResult.assume _ _ _ _ p (decp := decp)

def ConstrainedExtractResult.require_VeilM {m ρ σ ex} (p : Prop) [decp : Decidable p] :
  ConstrainedExtractResult Std.Format (VeilExecM m ρ σ) (VeilMultiExecM Std.Format ExId ρ σ)
  (findOfCandidates _) (@VeilM.require m ρ σ p decp ex) :=
  match m with
  | .external => ConstrainedExtractResult.assume_VeilM p (decp := decp)
  | .internal => ConstrainedExtractResult.liftM _ _ _ _ (@VeilExecM.assert m ρ σ p decp ex)

end VeilSpecificExtractionUtils

open MultiExtractor in
attribute [multiextracted] ConstrainedExtractResult.pure
  ConstrainedExtractResult.bind
  ConstrainedExtractResult.filterAuxM
  ConstrainedExtractResult.pick
  -- ConstrainedExtractResult.assume  -- This will be handled with a tactic
  -- ConstrainedExtractResult.pickList
  ConstrainedExtractResult.liftM ConstrainedExtractResult.ite
  ConstrainedExtractResult.pickSuchThat_VeilM
  ConstrainedExtractResult.assume_VeilM
  ConstrainedExtractResult.require_VeilM

open MultiExtractor in
attribute [multiExtractSimp ↓] ConstrainedExtractResult.pure
  ConstrainedExtractResult.bind ConstrainedExtractResult.assume
  ConstrainedExtractResult.filterAuxM
  ConstrainedExtractResult.pick
  ConstrainedExtractResult.pickList ConstrainedExtractResult.liftM ConstrainedExtractResult.ite
  ConstrainedExtractResult.val
  ConstrainedExtractResult.pickSuchThat_VeilM
  ConstrainedExtractResult.assume_VeilM
  ConstrainedExtractResult.require_VeilM

/-- Extract the execution outcome from a DivM-wrapped result. Unlike `getPostState`
which only returns `Option σ`, this preserves information about assertion failures
that can be used as counter-examples by the model checker. -/
@[inline]
def getExecutionOutcome (c : DivM ((Except ε α) × σ)) : Veil.ExecutionOutcome ε σ :=
  match c with
  | .res ((.ok _, st)) => .success st
  | .res ((.error e, st)) => .assertionFailure e st
  | .div => .divergence

/-- Extract the resulting post-state from a DivM-wrapped result pair. The
semantics of exceptions in Veil is that the whole computation is reverted, so
there is no post-state in the `error` case. -/
@[inline]
def getPostState (c : DivM ((Except ε α) × σ)) : Option σ :=
  getExecutionOutcome c |>.toPostState

def getAllPostStates (c : List (DivM ((Except ε α) × σ))) : List (Option σ) :=
  c.map getPostState

def getAllExecutionOutcomes (c : List (DivM ((Except ε α) × σ))) : List (Veil.ExecutionOutcome ε σ) :=
  c.map getExecutionOutcome

/-- Extract all valid states from a VeilMultiExecM computation -/
def extractValidStates (exec : Veil.VeilMultiExecM κᵣ ℤ ρ σ Unit) (rd : ρ) (st : σ) : List (Option σ) :=
  exec rd st |>.map Prod.snd |> getAllPostStates

/-- Extract all execution outcomes (including assertion failures) from a VeilMultiExecM computation -/
def extractAllOutcomes (exec : Veil.VeilMultiExecM κᵣ ℤ ρ σ Unit) (rd : ρ) (st : σ) : List (Veil.ExecutionOutcome ℤ σ) :=
  exec rd st |>.map Prod.snd |> getAllExecutionOutcomes

/-- Extract only assertion failures from a VeilMultiExecM computation.
Returns a list of (exception ID, state at failure) pairs. -/
def extractAssertionFailures (exec : Veil.VeilMultiExecM κᵣ ℤ ρ σ Unit) (rd : ρ) (st : σ) : List (ℤ × σ) :=
  extractAllOutcomes exec rd st |>.filterMap fun
    | .assertionFailure e s => some (e, s)
    | _ => none

def Module.assembleEnumerableTransitionSystem [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [MonadEnv m] [MonadOptions m] [AddMessageContext m] (mod : Module) : m Command := do
  mod.throwIfAlreadyDeclared enumerableTransitionSystemName

  -- Step 1: Use mkDerivedDefinitionsParamsMapFn pattern (like specializeActionsCore)
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .actionLike actionNames)

  -- HACK: filter out `ρ`, `σ`, `IsSubStateOf` and `IsSubReaderOf` from `baseParams`
  -- ... and put them at the beginning of `extraParams` instead
  let (baseParams, others) := baseParams.partition fun p => !(p.kind matches .environmentState | .backgroundTheory | .moduleTypeclass .environmentState | .moduleTypeclass .backgroundTheory)
  let theoryStx ← mod.theoryStx
  let stateStx ← mod.stateStx mod._useFieldRepTC
  let specializeToOther (p : Parameter) : Option Term :=
    match p.kind with
    | .environmentState => some stateStx
    | .backgroundTheory => some theoryStx
    | .moduleTypeclass .environmentState => some <| mkCIdent ``instIsSubStateOfRefl
    | .moduleTypeclass .backgroundTheory => some <| mkCIdent ``instIsSubReaderOfRefl
    | _ => none

  -- Step 2: Prepare injectedBinders
  let nextAct'Binders ← bindersToInjectForExecution mod
  let labelsId := mkVeilImplementationDetailIdent `labels
  let labelsBinder ← `(bracketedBinder| [$labelsId : $(mkIdent ``Veil.Enumeration) $(← mod.labelTypeStx)])
  let theoryId := mkVeilImplementationDetailIdent `theory
  let theoryBinder ← `(bracketedBinder| ($theoryId : $theoryStx))
  let injectedBinders := nextAct'Binders ++ #[labelsBinder, theoryBinder]

  -- Step 3: Build finalBody as struct literal
  let finalBody ← do
    let fieldConcrete ← `($fieldConcreteDispatcher $(← mod.sortIdents)*)
    let stateStx ← if mod._useFieldRepTC then `($stateIdent $fieldConcrete) else mod.stateStx
    let labelStx ← mod.labelTypeStx
    let (CInit, CNext) := (mkVeilImplementationDetailIdent `CInit, mkVeilImplementationDetailIdent `CNext)
    let (th, st) := (mkVeilImplementationDetailIdent `th, mkVeilImplementationDetailIdent `st)
    let (label, next) := (mkVeilImplementationDetailIdent `label, mkVeilImplementationDetailIdent `next)
    let filterMap ← `($(mkIdent ``List.filterMap) $(mkIdent ``id))

    -- NOTE: Use the `ext` version of `initializer` below!!!
    `({
      $(mkIdent `initStates):ident :=
        let $CInit := $(mkIdent <| toExtractedName <| toExtName initializerName) $theoryStx $stateStx $(← mod.sortIdents)*
        $(mkIdent ``extractValidStates) $CInit $theoryId $(mkIdent ``default) |> $filterMap
      $(mkIdent `tr):ident := fun $th $st =>
        let $CNext := $(mkIdent <| toExtractedName assembledNextActName) $theoryStx $stateStx $(← mod.sortIdents)*
        $(mkIdent ``List.flatMap) (fun ($label : $labelStx) =>
         $(mkIdent ``List.map) (fun $next => ($label, $next)) ($(mkIdent ``extractAllOutcomes) ($CNext $label) $th $st))
         (@$(mkIdent ``Veil.Enumeration.allValues) _ $labelsId)
      : $(mkIdent ``Veil.EnumerableTransitionSystem)
        $theoryStx ($(mkIdent ``List) $theoryStx)
        $stateStx ($(mkIdent ``List) $stateStx)
        $(mkIdent ``Int)
        $labelStx ($(mkIdent ``List) ($labelStx × $(mkIdent ``Veil.ExecutionOutcome) $(mkIdent ``Int) $stateStx))
        $theoryId
     })

  -- Step 4: Specialize `χ`, `χ_rep`, `χ_rep_lawful` and build the term
  let enumerableTransitionSystemTerm ← buildingTermWithDefaultχSpecialized baseParams (others ++ extraParams)
    injectedBinders finalBody mod specializeToOther

  -- Step 5: Add @[specialize] attribute
  `(command| @[specialize] def $enumerableTransitionSystem:ident := $enumerableTransitionSystemTerm)

end Veil.Extract
