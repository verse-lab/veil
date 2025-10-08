import Veil.Frontend.DSL.Action.Extraction.Basic
import Veil.Frontend.DSL.Action.Extraction.Util
import Veil.Frontend.DSL.Module.Util

open Lean Elab Command Term Meta Lean.Parser

namespace Veil

def Module.generateVeilMultiExecM -- [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [MonadOptions m] [AddMessageContext m]
  (mod : Module) (κ extractNonDet : TSyntax `term)
  (injectedBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))     -- FIXME: __THIS IS A HACK__
  (useWeak : Bool := true) : CommandElabM Unit := do

  -- prepare the names
  let initExecIdent := mkIdent `initMultiExec
  let nextExtractIdent := mkIdent `nextMultiExtract
  let nextActExecIdent := mkIdent `nextActMultiExec
  let findable := mkIdent <| (if useWeak then ``MultiExtractor.PartialCandidates else ``MultiExtractor.Candidates)
  let extractor := mkIdent <| (if useWeak then ``NonDetT.extractPartialList else ``NonDetT.extractList)

  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  -- TODO where to eliminate the `Decidable` instances?
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .actionLike actionNames)
  -- TODO this is somehow cutting a shortpath for `initializer`, but this
  -- might not be a proper way to do this
  let binders ← (baseParams ++ extraParams).mapM (·.binder)
  let binders' := binders ++ injectedBinders

  let overallArgs ← (baseParams ++ extraParams).mapM (·.arg)

  let unitIdent := mkIdent `Unit
  -- let acts ← mod.actions.mapM (fun s => do
  --   let name := Lean.mkIdent $ toExtName s.name
  --   let (params, _) ← mod.declarationAllParams s.name s.declarationKind
  --   let args ← params.mapM (·.arg)
  --   `(@$name $args*))

  -- build `initMultiExec`
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
  let lIdent := mkIdent `l
  let alts ← mod.actions.mapM (fun a => do
    match a.params with
    | some br =>
      let tmp ← explicitBindersToTerms br
      `(term| (fun $tmp* => $extractNonDet))
    | none => `(term| ($extractNonDet)))
  let target1 := Syntax.mkApp (← `(term| @$assembledNextAct)) (overallArgs.push lIdent)
  let nextExtractFuncCmd ← `(
    def $nextExtractIdent $[$binders']* : ∀ $lIdent,
      $(mkIdent ``MultiExtractor.ExtractNonDet)
      ($(mkIdent ``MultiExtractor.ExtCandidates) $findable ($κ))
      ($target1) := fun $lIdent => $lIdent.$(mkIdent `casesOn) $alts*
  )

  -- build `nextActExec`
  let overallArgs' := overallArgs ++ (← bracketedBindersToTerms injectedBinders)
  let overallArgs'' := overallArgs'.push lIdent
  let target2 := Syntax.mkApp (← `(term| @$nextExtractIdent)) overallArgs''
  let nextActExecCmd ← `(
    def $nextActExecIdent $[$binders']* :=
      fun $lIdent => $extractor ($κ)
        ($(mkIdent ``VeilMultiExecM) ($κ) ExId $environmentTheory $environmentState)
        ($target1) ($target2)
  )
  elabVeilCommand initExecCmd
  elabVeilCommand nextExtractFuncCmd
  elabVeilCommand nextActExecCmd

-- @[inherit_doc generateVeilMultiExecM]
elab "#gen_executable_list" weak:("!")? logelem:term
  "injection_begin" injectedBinders:bracketedBinder* "injection_end" : command => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  let tac ← `(term| by (open $(mkIdent `MultiExtractor):ident in extract_list_tactic))
  mod.generateVeilMultiExecM logelem tac injectedBinders weak.isNone

end Veil
