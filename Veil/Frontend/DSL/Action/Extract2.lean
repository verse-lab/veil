import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Action.ExtractList2
import Veil.Frontend.DSL.Action.Extract

open Lean Elab Command Term Meta Lean.Parser

namespace Veil.Extract

-- TODO **THIS CODE IS JUST FOR EXPERIMENTAL PURPOSES**
def generateVeilMultiExecMCore2 (κ : TSyntax `term)
  (injectedBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))     -- FIXME: __THIS IS A HACK__ ; similar above, and this is intended to be passed the same things as above
  (target : Option Ident) (useWeak : Bool) : CommandElabM Unit := do
  let mod ← getCurrentModule
  -- prepare the names
  let initExecIdent := mkIdent `initMultiExec
  let nextActExecIdent := mkIdent `nextActMultiExec
  let extractor := mkIdent <| (if useWeak then ``MultiExtractor.NonDetT.extractPartialList2 else ``MultiExtractor.NonDetT.extractList2)
  let unitIdent := mkIdent `Unit
  -- similar to `Module.specializeActions`
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .actionLike actionNames)
  -- TODO this is somehow cutting a shortpath for `initializer` (meaning
  -- `baseParams` is only computed once), but this might not be a proper way
  -- to do this

  let multiExecMonadType ← `(term| $(mkIdent ``VeilMultiExecM) ($κ) ExId $environmentTheory $environmentState)
  let multiExecType := Syntax.mkApp multiExecMonadType #[unitIdent]
  let buildExtractBody (body : TSyntax `term) : CommandElabM (TSyntax `term) := do
    let extractSimps : Array Ident :=
      #[``MultiExtractor.NonDetT.extractList2, ``MultiExtractor.ExtractConstraint.get, ``instMonadLiftT,
        ``id, ``inferInstance, ``inferInstanceAs, instFieldRepresentationName].map Lean.mkIdent
    `(veil_dsimp% -$(mkIdent `zeta) -$(mkIdent `failIfUnchanged) [$[$extractSimps:ident],*]
      ($extractor ($κ) _ _ ($body)))

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
    let bd ← buildExtractBody (← `(@$initComputableIdent $initArgs*))
    `(def $initExecIdent $[$initBinders']* : $multiExecType := $bd)

  -- build `nextExtract`
  -- NOTE: since this works on `NextAct` or its specialized version, this needs
  -- to be specified as well
  let lIdent := mkIdent `l
  let labelT ← mod.labelTypeStx
  let nextActExecCmd ← do
    if let some tg := target then
      let overallArgs ← do
        -- TODO **FIX THIS ADHOC CODE**
        let idx := baseParams.findIdx fun p => p.kind == .fieldConcreteType
        let tmp1 ← baseParams.take idx |>.mapM (·.arg)
        let tmp2 ← bracketedBindersToTerms injectedBinders
        let tmp3 ← baseParams.drop (3 + idx) |>.mapM (·.arg)
        let tmp4 ← extraParams.mapM (·.arg)
        pure (tmp1 ++ tmp2 ++ tmp3 ++ tmp4)
      let target1 := Syntax.mkApp (← `(term| @$tg )) overallArgs

      let localSimps : Array Ident :=
        #[`Veil.VeilM.returnUnit].map Lean.mkIdent |>.push tg
      let alts ← mod.actions.mapM fun a => do
        let args ← a.params.mapM (·.arg)
        let lbl ← `($(mkIdent <| labelTypeName ++ a.name) $args*)  -- adhoc
        let body ← do
          let tmp ← `(veil_dsimp% -$(mkIdent `zeta) -$(mkIdent `failIfUnchanged) [$[$localSimps:ident],*] $(Syntax.mkApp target1 #[lbl]))
          buildExtractBody tmp
        mkFunSyntax args body

      let finalBody ← `(fun ($lIdent : $labelT) =>
        (($lIdent.$(mkIdent `casesOn) $alts*) : $multiExecType))
      let cmd ← Specialization.buildingTermWithχSpecialized baseParams extraParams injectedBinders nextActExecIdent finalBody
        (← `(term| _ ))
        (← `(term| $instFieldRepresentation $(← mod.sortIdents)* ))
        (← `(term| _ ))
      pure cmd
    else
      let binders ← do
        let tmp1 ← baseParams.mapM (·.binder)
        let tmp2 ← extraParams.mapM (·.binder)
        pure <| tmp1 ++ injectedBinders ++ tmp2
      let overallArgs ← (baseParams ++ extraParams).mapM (·.arg)
      let target1 := Syntax.mkApp (← `(term| @$assembledNextAct)) overallArgs

      -- TODO repetition
      let localSimps : Array Ident :=
        #[`Veil.VeilM.returnUnit].map Lean.mkIdent |>.push assembledNextAct
      let alts ← mod.actions.mapM fun a => do
        let args ← a.params.mapM (·.arg)
        let lbl ← `($(mkIdent <| labelTypeName ++ a.name) $args*)  -- adhoc
        let body ← do
          let tmp ← `(veil_dsimp% -$(mkIdent `zeta) -$(mkIdent `failIfUnchanged) [$[$localSimps:ident],*] $(Syntax.mkApp target1 #[lbl]))
          buildExtractBody tmp
        mkFunSyntax args body

      let cmd ← `(def $nextActExecIdent $[$binders]* ($lIdent : $labelT) : $multiExecType :=
        $lIdent.$(mkIdent `casesOn) $alts*
      )
      pure cmd

  elabVeilCommand initExecCmd
  elabVeilCommand nextActExecCmd

syntax (name := generateVeilMultiExecMStx2) "#gen_executable_list2" ("!")? "log_entry_being" term
  ("targeting" ident)? (injectBindersStx)? : command

elab_rules : command
  | `(#gen_executable_list2! log_entry_being $logelem:term targeting $target:ident injection_begin $injectedBinders:bracketedBinder* injection_end) => do
    generateVeilMultiExecMCore2 logelem injectedBinders (some target) false
  -- FIXME: the other cases

def genExtractCommand2 (binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) : CommandElabM Unit := do
  let execListCmd ← `(command |
    #gen_executable_list2! log_entry_being $(mkIdent ``Std.Format)
    targeting $nextActSimplified
    injection_begin
      $[$binders]*
    injection_end)
  trace[veil.debug] "gen_executable_NextAct: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic execListCmd}"
  elabVeilCommand execListCmd

end Veil.Extract
