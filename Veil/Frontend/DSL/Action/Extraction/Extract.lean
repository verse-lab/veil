import Veil.Frontend.DSL.Action.Extraction.Basic
import Veil.Frontend.DSL.Action.Extraction.Util
import Veil.Frontend.DSL.Module.Util

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
    if binders.isEmpty then pure finalBody else `(fun $[$binders]* => $finalBody)
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
    (mkIdent ``inferInstance)
    (mkIdent ``inferInstance)

def specializeActions (χ target : Ident) (extraDsimps : TSyntaxArray `ident)
  (injectedBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) : CommandElabM Unit := do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
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
  let initExecIdent := mkIdent `initMultiExec
  let nextExtractIdent := mkIdent `nextMultiExtract
  let nextActExecIdent := mkIdent `nextActMultiExec
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
    let initComputable ← resolveGlobalConstNoOverloadCore initializerName
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
    | some br =>
      let tmp ← explicitBindersToTerms br
      `(term| (fun $tmp* => $extractNonDet))
    | none => `(term| ($extractNonDet)))
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

end Veil.Extract
