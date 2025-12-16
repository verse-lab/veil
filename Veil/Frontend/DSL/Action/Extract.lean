import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Action.ExtractUtil
import Veil.Frontend.DSL.Module.Names

open Lean Elab Command Term Meta Lean.Parser

namespace Veil.Extract

syntax injectBindersStx := "injection_begin" bracketedBinder* "injection_end"

namespace Preprocessing

attribute [dsimpFieldRepresentationGet ↓] FieldRepresentation.get FieldRepresentation.mkFromSingleSet instFinsetLikeAsFieldRep IteratedArrow.curry
  Equiv.coe_fn_mk Function.comp IteratedProd'.equiv IteratedProd.toIteratedProd'
attribute [dsimpFieldRepresentationSet ↓] FieldRepresentation.setSingle FieldRepresentation.mkFromSingleSet instFinsetLikeAsFieldRep FieldRepresentation.FinsetLike.setSingle'
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

namespace Specialization

def buildingTermWithχSpecialized
  [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [MonadOptions m] [AddMessageContext m]
  (baseParams extraParams : Array Parameter)
  (injectedBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
  (target : Ident)
  (finalBody χ χ_rep χ_rep_lawful : Term) : m Command := do
  -- do some segmentation here
  -- NOTE: here implicitly assume that `χ`, `χ_rep`, `χ_rep_lawful` are contiguous
  let (baseParamsNoχPrefix, baseParamsSuffix, χ_ty, χ_rep_ty, χ_rep_lawful_ty) :=
    let idx := baseParams.findIdx fun p => p.kind == .fieldConcreteType
    (baseParams.take idx, baseParams.drop (3 + idx),
      baseParams[idx]!.type, baseParams[idx + 1]!.type, baseParams[idx + 2]!.type)
  let preBinders := (← baseParamsNoχPrefix.mapM (·.binder)) ++ injectedBinders
  let sufBinders ← baseParamsSuffix.mapM fun (a : Parameter) => a.binder >>= bracketedBinderToFunBinder
  let extraBinders ← extraParams.mapM fun (a : Parameter) => a.binder >>= bracketedBinderToFunBinder
  -- build the while `def`
  let body1 ← do
    let binders := sufBinders ++ extraBinders
    mkFunSyntax binders finalBody
  -- let body2 ← do
  let body2 ← `(
    letI $fieldConcreteType : $χ_ty := $χ
    letI $fieldRepresentation : $χ_rep_ty := $χ_rep
    letI $lawfulFieldRepresentation : $χ_rep_lawful_ty := $χ_rep_lawful
    $body1)
  `(command|def $target $[$preBinders]* := $body2)

/-- Similar to `Module.assembleNext`, but specializes the concrete type.
The corresponding `FieldRepresentation` and `LawfulFieldRepresentation`
instances shall be synthesized. -/
def specializeActionsCore
  [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [MonadOptions m] [AddMessageContext m]
  (mod : Module) (χ target : Ident) (extraDsimps : TSyntaxArray `ident)
  (injectedBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) : m Command := do
  unless mod._useFieldRepTC do
    throwError "[{decl_name%}]: module does not use field representations"
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .actionLike actionNames)
  let acts ← mod.actions.mapM fun s => do
    let name := Lean.mkIdent $ toExtName s.name
    let (params, _) ← mod.declarationAllParams s.name s.declarationKind
    let args ← params.mapM (·.arg)
    `(veil_dsimp% -$(mkIdent `zeta) -$(mkIdent `failIfUnchanged)
      [$(mkIdent ``Preprocessing.simpFieldRepresentationSetSingle),
       $(mkIdent ``Preprocessing.simpFieldRepresentationGet),
       $(mkIdent ``id),
       $[$extraDsimps:ident],*]
      (delta% (@$name $args*)))
  let labelT ← mod.labelTypeStx
  let label := mkIdent `label
  let finalBody ← `(fun ($label : $labelT) =>
    (($label.$(mkIdent `casesOn) $acts*) : $(mkIdent ``VeilM) $(mkIdent ``Mode.external) $environmentTheory $environmentState $(mkIdent ``Unit)))
  buildingTermWithχSpecialized baseParams extraParams injectedBinders target finalBody
    (← `(($χ $(← mod.sortIdents)*)))
    (← `($instFieldRepresentation $(← mod.sortIdents)*))
    (← `($instLawfulFieldRepresentation $(← mod.sortIdents)*))

def specializeActions (χ target : Ident) (extraDsimps : TSyntaxArray `ident)
  (injectedBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) : CommandElabM Unit := do
  let mod ← getCurrentModule
  let cmd ← specializeActionsCore mod χ target extraDsimps injectedBinders
  elabVeilCommand cmd

syntax (name := specializeNextActStx) "#specialize_nextact " "with" ident
  ("dsimp_with " "[" ident,* "]")? (injectBindersStx)? "=>" ident : command

elab_rules : command
  | `(#specialize_nextact with $χ:ident dsimp_with [$[$extraDsimps:ident],*] injection_begin $injectedBinders:bracketedBinder* injection_end => $target:ident) => do
    specializeActions χ target extraDsimps injectedBinders
  | `(#specialize_nextact with $χ:ident dsimp_with [$[$extraDsimps:ident],*] => $target:ident) => do
    specializeActions χ target extraDsimps #[]
  | `(#specialize_nextact with $χ:ident injection_begin $injectedBinders:bracketedBinder* injection_end => $target:ident) => do
    specializeActions χ target #[] injectedBinders
  | `(#specialize_nextact with $χ:ident => $target:ident) => do
    specializeActions χ target #[] #[]

end Specialization

def generateVeilMultiExecMCore (κ extractNonDet : TSyntax `term)
  (injectedBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))     -- FIXME: __THIS IS A HACK__ ; similar above, and this is intended to be passed the same things as above
  (target : Option Ident) (useWeak : Bool) : CommandElabM Unit := do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  -- prepare the names
  let findable := mkIdent <| (if useWeak then ``MultiExtractor.PartialCandidates else ``MultiExtractor.Candidates)
  let extractor := mkIdent <| (if useWeak then ``NonDetT.extractPartialList else ``NonDetT.extractList)
  let unitIdent := mkIdent `Unit
  -- similar to `Module.specializeActions`
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .actionLike actionNames)
  -- TODO this is somehow cutting a shortpath for `initializer` (meaning
  -- `baseParams` is only computed once), but this might not be a proper way
  -- to do this

  -- build `initMultiExec`
  -- NOTE: ideally we might also use a specialized version of `initializer`,
  -- but it should not be critical for the performance, so we just use the
  -- original one here
  let initExecCmd ← do
    let initComputable ← resolveGlobalConstNoOverloadCore (toExtName initializerName)
    let initComputableIdent := mkIdent initComputable
    let initExtraParams := Array.flatten <|
      mod.procedures.filterMap (fun a => if initializerName == a.name then .some a.extraParams else .none)
    let initBinders ← (baseParams ++ initExtraParams).mapM (·.binder)
    let initBinders' := initBinders ++ injectedBinders
    let initArgs ← do
      let (params, _) ← mod.declarationAllParams initializerName (.procedure .initializer)
      params.mapM (·.arg)
    `(def $initExecIdent $[$initBinders']* :
      $(mkIdent ``VeilMultiExecM) ($κ) ExId $environmentTheory $environmentState $unitIdent :=
      ($extractor ($κ) _ (@$initComputableIdent $initArgs*) $extractNonDet))

  -- build `nextExtract`
  -- NOTE: since this works on `NextAct` or its specialized version, this needs
  -- to be specified as well
  let lIdent := mkIdent `l
  let labelT ← mod.labelTypeStx
  let alts ← mod.actions.mapM (fun a => do
    match a.params with
    | #[] => `(term| ($extractNonDet))
    | params => do
      let tmp ← params.mapM (·.arg)
      mkFunSyntax tmp extractNonDet)
  let (binders?, overallArgs, target1, nextExtractFuncCmd) ← do
    if let some tg := target then
      let overallArgs ← do
        let idx := baseParams.findIdx fun p => p.kind == .fieldConcreteType
        let tmp1 ← baseParams.take idx |>.mapM (·.arg)
        let tmp2 ← bracketedBindersToTerms injectedBinders
        let tmp3 ← baseParams.drop (3 + idx) |>.mapM (·.arg)
        let tmp4 ← extraParams.mapM (·.arg)
        pure <| (tmp1 ++ tmp2 ++ tmp3 ++ tmp4).push lIdent
      let target1 := Syntax.mkApp (← `(term| @$tg )) overallArgs
      let finalBody ← `(fun ($lIdent : $labelT) =>
        (($lIdent.$(mkIdent `casesOn) $alts*) :
          $(mkIdent ``MultiExtractor.ExtractNonDet)
          ($(mkIdent ``MultiExtractor.ExtCandidates) $findable ($κ))
          ($target1)))
      let cmd ← Specialization.buildingTermWithχSpecialized baseParams extraParams injectedBinders nextExtractIdent finalBody
        (← `(term| _ ))
        (← `(term| _ ))
        (← `(term| _ ))
      pure (Option.none, overallArgs, target1, cmd)
    else
      let binders ← do
        let tmp1 ← baseParams.mapM (·.binder)
        let tmp2 ← extraParams.mapM (·.binder)
        pure <| tmp1 ++ injectedBinders ++ tmp2
      let overallArgs ← (baseParams ++ extraParams).mapM (·.arg)
      let target1 := Syntax.mkApp (← `(term| @$assembledNextAct)) (overallArgs.push lIdent)
      let cmd ← `(def $nextExtractIdent $[$binders]* : ∀ $lIdent,
          $(mkIdent ``MultiExtractor.ExtractNonDet)
          ($(mkIdent ``MultiExtractor.ExtCandidates) $findable ($κ))
          ($target1) := fun $lIdent => $lIdent.$(mkIdent `casesOn) $alts*
      )
      pure (Option.some binders, overallArgs, target1, cmd)
  let nextActExecCmd ← do
    if let some binders := binders? then
      let target2 := Syntax.mkApp (← `(term| @$nextExtractIdent)) overallArgs
      `(def $nextActExecIdent $[$binders]* :=
          fun $lIdent => $extractor ($κ)
            ($(mkIdent ``VeilMultiExecM) ($κ) ExId $environmentTheory $environmentState)
            ($target1) ($target2)
      )
    else
      let target2 := Syntax.mkApp (← `(term| @$nextExtractIdent)) overallArgs
      let finalBody ←
      `(fun ($lIdent : $labelT) => $extractor ($κ)
        ($(mkIdent ``VeilMultiExecM) ($κ) ExId $environmentTheory $environmentState)
        ($target1) ($target2)
      )
      Specialization.buildingTermWithχSpecialized baseParams extraParams injectedBinders nextActExecIdent finalBody
        (← `(term| _ ))
        (← `(term| _ ))
        (← `(term| _ ))

  elabVeilCommand initExecCmd
  elabVeilCommand nextExtractFuncCmd
  elabVeilCommand nextActExecCmd

syntax (name := generateVeilMultiExecMStx) "#gen_executable_list" ("!")? "log_entry_being" term
  ("targeting" ident)? (injectBindersStx)? : command

elab_rules : command
  | `(#gen_executable_list! log_entry_being $logelem:term targeting $target:ident injection_begin $injectedBinders:bracketedBinder* injection_end) => do
    let tac ← `(term| by (open $(mkIdent `MultiExtractor):ident in extract_list_tactic))
    generateVeilMultiExecMCore logelem tac injectedBinders (some target) false
  -- FIXME: the other cases

/-- Generate both NextAct specialization and executable list commands. -/
def genNextActCommands (mod : Veil.Module) : CommandElabM Unit := do
  let binders ← mod.collectNextActBinders
  -- Generate NextAct specialization
  let nextActCmd ← `(command |
    attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet] $instEnumerationForIteratedProd in
    #specialize_nextact with $fieldConcreteDispatcher
    injection_begin
      $[$binders]*
    injection_end => $nextActSimplified
    )
  trace[veil.debug] "gen_NextAct: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic nextActCmd}"
  elabVeilCommand nextActCmd

  -- Generate executable list
  let execListCmd ← `(command |
    #gen_executable_list! log_entry_being $(mkIdent ``Std.Format)
    targeting $nextActSimplified
    injection_begin
      $[$binders]*
    injection_end)
  trace[veil.debug] "gen_executable_NextAct: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic execListCmd}"
  elabVeilCommand execListCmd

/-- Extract the resulting state from an ExceptT-wrapped execution, if successful. -/
def getStateFromExceptT (c : ExceptT ε DivM (α × σ)) : Option σ :=
  match c.run with
  | .res (.ok (_, st)) => .some st
  | .res (.error _)    => .none
  | .div => none

def getAllStatesFromExceptT (c : List (ExceptT ε DivM (α × σ))) : List (Option σ) :=
  c.map getStateFromExceptT

/-- Extract all valid states from a VeilMultiExecM computation -/
def extractValidStates (exec : Veil.VeilMultiExecM κᵣ ℤ ρ σ Unit) (rd : ρ) (st : σ) : List (Option σ) :=
  exec rd st |>.map Prod.snd |> getAllStatesFromExceptT

def Module.assembleEnumerableTransitionSystem [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] (mod : Module) : m Command := do
  mod.throwIfAlreadyDeclared enumerableTransitionSystemName

  -- Step 1: Use mkDerivedDefinitionsParamsMapFn pattern (like specializeActionsCore)
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .actionLike actionNames)

  -- HACK: filter out `ρ`, `σ`, `IsSubStateOf` and `IsSubReaderOf` from `baseParams`
  let baseParams := baseParams.filter fun p => !(p.kind matches .environmentState | .backgroundTheory | .moduleTypeclass .environmentState | .moduleTypeclass .backgroundTheory)

  -- Step 2: Prepare injectedBinders
  let nextAct'Binders ← mod.collectNextActBinders
  let labelsId := mkVeilImplementationDetailIdent `labels
  let labelsBinder ← `(bracketedBinder| [$labelsId : $(mkIdent ``Veil.Enumeration) $(← mod.labelTypeStx)])
  let theoryId := mkVeilImplementationDetailIdent `theory
  let theoryStx ← mod.theoryStx
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

    `({
      initStates :=
        let $CInit := $initExecIdent $theoryStx $stateStx $(← mod.sortIdents)* $fieldConcrete
        $(mkIdent ``extractValidStates) $CInit $theoryId $(mkIdent ``default) |> $filterMap
      tr := fun $th $st =>
        let $CNext := $nextActExecIdent $theoryStx $stateStx $(← mod.sortIdents)*
        $(mkIdent ``List.flatMap) (fun ($label : $labelStx) =>
         $(mkIdent ``List.map) (fun $next => ($label, $next)) ($(mkIdent ``extractValidStates) ($CNext $label) $th $st |> $filterMap))
         (@$(mkIdent ``Veil.Enumeration.allValues) _ $labelsId)
      : $(mkIdent ``Veil.EnumerableTransitionSystem)
        $theoryStx ($(mkIdent ``List) $theoryStx)
        $stateStx ($(mkIdent ``List) $stateStx)
        $labelStx ($(mkIdent ``List) ($labelStx × $stateStx))
        $theoryId
     })

  -- Step 4: Call buildingTermWithχSpecialized (using explicit instances like specializeActionsCore)
  let defCmd ← Specialization.buildingTermWithχSpecialized baseParams extraParams
    injectedBinders enumerableTransitionSystem finalBody
    (← `(($fieldConcreteDispatcher $(← mod.sortIdents)*)))
    (← `($instFieldRepresentation $(← mod.sortIdents)*))
    (← `($instLawfulFieldRepresentation $(← mod.sortIdents)*))

  -- Step 5: Add @[specialize] attribute
  match defCmd with
  | `(command| def $name:ident $binders* := $body) =>
    `(command| @[specialize] def $name:ident $binders* := $body)
  | _ => return defCmd

end Veil.Extract
