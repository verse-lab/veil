module

public meta import Veil.Frontend.DSL.Module.Util
public meta import Veil.Frontend.DSL.Module.Names
public import Veil.Core.Tools.ModelChecker.ExecutionOutcome
public import Veil.Frontend.DSL.Action.Semantics.WP

public import Veil.Frontend.DSL.State.Types

public section

open Lean Elab Command Term Meta Lean.Parser

namespace Veil.Extract

meta section FrontendExtraction

syntax injectBindersStx := "injection_begin" bracketedBinder* "injection_end"

namespace Preprocessing

attribute [dsimpFieldRepresentationGet ↓] FieldRepresentation.get
  instFinmapLikeAsFieldRep IteratedArrow.curry
  Equiv.coe_fn_mk Function.comp IteratedProd'.equiv IteratedProd.toIteratedProd'
attribute [dsimpFieldRepresentationSet ↓] FieldRepresentation.setSingle
  instFinmapLikeAsFieldRep FieldRepresentation.FinmapLike.setSingle'
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
  -- Not `.done`: when this runs before the subterms are visited (as in `veil_dsimp%`),
  -- that would skip the arguments `e` is applied to, which can hold reads as well
  -- (`pc (nxt i)` in a `Decidable` instance).
  return .continue res.expr

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

/-- A term built by `buildingTermWithInjectionAndParameterSpecialized`, together
with the call convention its binder structure implies.

Specializing a parameter turns it into a `letI` rather than a binder, so a caller
must not supply it. Both fields are read off the same segmentation, and the
constructor is private, so the two cannot disagree. -/
structure SpecializedTerm where
  private mk ::
  /-- The definition's body. -/
  body : Term
  /-- The binders a call site supplies positionally, in order. -/
  explicitParams : Array Parameter

/-- Apply a specialized definition to the arguments its binders call for. The
parameters keep the names they were bound under, so this is the call to make
from inside a definition that binds the same parameters. -/
def SpecializedTerm.callSyntax [Monad m] [MonadQuotation m] (d : SpecializedTerm) (f : Ident) : m Term := do
  `($f $(← d.explicitParams.mapM (·.arg))*)

section Specialization

variable [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [AddErrorMessageContext m] [MonadTrace m] [MonadOptions m] [AddMessageContext m]
  (baseParams extraParams : Array Parameter)
  (injectedBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
  (finalBody : Term)

def buildingTermWithInjectionAndParameterSpecialized
  (specializedTo : Parameter → Option Term) : m SpecializedTerm := do
  let baseSegments := segmentingParameters baseParams
  let extraSegments := segmentingParameters extraParams
  let body ← do
    let part1 ← mkFunctionWithSegments extraSegments finalBody
    let part2 ← `(remove_unused_binders% $injectedBinders* => $part1)
    mkFunctionWithSegments baseSegments part2
  -- Read the call convention off the same segmentation that emitted the
  -- binders: `Sum.inl` segments became binders, `Sum.inr` ones became `letI`s.
  -- `mkFunctionWithSegments` puts the base binders outside the extra ones, so
  -- this order matches the order arguments are applied in. The injected binders
  -- in between are all instance binders, so they are never positional.
  let binderParams (segs : Array (Sum (Array Parameter) (Parameter × Term))) : Array Parameter :=
    segs.flatMap fun seg => match seg with | .inl ps => ps | .inr _ => #[]
  -- NOTE: We cannot simply switch `callSyntax` to `@` and pass all these parameters:
  -- injected binders are absent from these segments, and `remove_unused_binders%`
  -- drops unused ones. Ordinary application lets Lean infer the retained instances.
  let explicit := (binderParams baseSegments ++ binderParams extraSegments).filter (·.isExplicit)
  return ⟨body, explicit⟩
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
  (specializedToOther : Parameter → Option Term := fun _ => none) : m SpecializedTerm := do
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
  (specializedToOther : Parameter → Option Term := fun _ => none) : m SpecializedTerm := do
  buildingTermWithχSpecialized baseParams extraParams injectedBinders finalBody
    (← `(($fieldConcreteDispatcher $(← mod.uninterpretedParamIdents)*)))
    (← `($instFieldRepresentation $(← mod.uninterpretedParamIdents)*))
    (← `($instLawfulFieldRepresentation $(← mod.uninterpretedParamIdents)*))
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
  if targets.isEmpty then return
  let simps := #[``Preprocessing.simpFieldRepresentationSetSingle, ``Preprocessing.simpFieldRepresentationGet].map Lean.mkIdent
  evalTactic <| ← `(tactic| dsimp -$(mkIdent `failIfUnchanged) only [$[$simps:ident],*] at $targets:ident* )

/-- `veil_dsimp_field_reads% t` simplifies the field reads in `t`, instance
arguments included.

It wraps the call that runs the model checker. That call is where the
`Decidable` instances of invariants, and of the `require` conditions that
actions take as instance parameters, are synthesized for the concrete field
representation. Otherwise each read in them,
`FieldRepresentation.get (instFieldRepresentation … f) fc`, would rebuild
the representation of field `f` and go through its generic `get` every time
the condition is checked. -/
macro (name := dsimpFieldReadsStx) "veil_dsimp_field_reads% " t:term : term =>
  `(veil_dsimp% -$(mkIdent `zeta) +$(mkIdent `instances)
    [$(mkIdent ``Preprocessing.simpFieldRepresentationGet)] $t)

open Tactic in
/--
Run Loom's extraction tactic, but turn leftover generated proof goals into a
short Veil-facing diagnostic. In particular, this avoids Lean's noisy
"could not synthesize default value" report when a `let x :| p` ranges over a
type that cannot be enumerated.
-/
scoped elab "veil_extract_list_tactic" : tactic => do
  let tac ←
    if veil.extract.shareValueLets.get (← getOptions)
    then `(tactic| extract_list_step +$(mkIdent `shareValueLets))
    else `(tactic| extract_list_step -$(mkIdent `shareValueLets))
  evalTactic (← `(tactic|
    repeat' (intros; first | $tac:tactic | (split <;> try dsimp))))
  unless (← getUnsolvedGoals).isEmpty do
    throwError
      "could not extract executable choices for a nondeterministic pick.\n\n\
      A `let x :| p` choice must have finitely enumerable candidates. \
      Provide a `Veil.Enumeration`/`MultiExtractor.Candidates` instance for \
      the picked type, or use a finite/enumerated type instead of an infinite \
      type such as `Nat`."

section Extraction

variable [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [AddErrorMessageContext m]
  (injectedBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (extraDsimpsForSpecialize : TSyntaxArray `ident)
  (κ : TSyntax `term) (useWeak intoMonadicActions : Bool)

def specializeAndExtractCore
  (actName : Name) (allParams : Array Parameter) : m Term := do
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
  let extraDsimpsForSpecialize := extraDsimpsForSpecialize.push <| Lean.mkIdent ``id
  -- `+instances`: the `Decidable` instances synthesized inside the action (e.g.
  -- for `require` on a ghost relation) read fields too
  `(veil_dsimp% -$(mkIdent `zeta) -$(mkIdent `failIfUnchanged) +$(mkIdent `instances)
    [$(mkIdent ``Preprocessing.simpFieldRepresentationSetSingle),
    $(mkIdent ``Preprocessing.simpFieldRepresentationGet),
    $(mkIdent `Veil.VeilM.returnUnit),
    $[$extraDsimpsForSpecialize:ident],*]
    (delta% $fullyAppliedAction))
 buildExtractBody (body bodyBeforeSimp : Term) : m Term := do
  let multiExecMonadType ← `(term| $(mkIdent ``VeilMultiExecM) ($κ) ExId $environmentTheory $environmentState)
  let extractor := mkIdent <| (if useWeak then ``MultiExtractor.NonDetT.extractPartialList else ``MultiExtractor.NonDetT.extractList)
  -- HACK: when not `intoMonadicActions`, `targetType` is actually partial
  let targetType ← if intoMonadicActions then `($multiExecMonadType Unit)
    else
      let tmp ← if useWeak
        then `(term| $(mkIdent ``MultiExtractor.findOfPartialCandidates) _)
        else `(term| $(mkIdent ``MultiExtractor.findOfCandidates) _)
      `(term| $(mkIdent ``MultiExtractor.ConstrainedExtractResult) ($κ) _ ($multiExecMonadType) ($tmp))
  let extractSimps : Array Ident :=
    #[`multiExtractSimp, ``instMonadLiftT,
      -- NOTE: The following are added to work around a bug (?) fixed in Lean v4.27.0-rc1
      ``id, ``inferInstance, ``«inferInstanceAs», instFieldRepresentationName].map Lean.mkIdent
  let extractSimps := if intoMonadicActions then extractSimps.push extractor else extractSimps
  -- Give the computational `by` block a type before running its tactics. Public
  -- definitions in the module system postpone tactics whose goal still has metavariables.
  let extractedBody ← if intoMonadicActions then
      `((by
          veil_dsimp_decidable_instances_before_extraction
          exact $extractor ($κ) _ _ ($body) (h := by veil_extract_list_tactic) : $targetType))
    -- Use the first `show` to have more concise type information that can be
    -- registered to the discrimination tree.
    else `(show $targetType ($bodyBeforeSimp) from by
      veil_dsimp_decidable_instances_before_extraction
      exact (show $targetType ($body) by veil_extract_list_tactic))
  `((veil_dsimp% -$(mkIdent `zeta) -$(mkIdent `failIfUnchanged) [$[$extractSimps:ident],*]
    ($extractedBody)))

def specializeAndExtractSingle (mod : Module) (pi : ProcedureInfo) (extractedName : Name := toExtractedName pi.name)
  (attrs : Array (TSyntax ``Lean.Parser.Term.attrInstance) := #[])
  (toExtract : Name := pi.name) : CommandElabM SpecializedTerm := do
  let (baseParams, extraParams, actualParams) ← mod.declarationSplitParams pi.name (.procedure pi)
  let extractBody ← specializeAndExtractCore extraDsimpsForSpecialize κ useWeak intoMonadicActions toExtract (baseParams ++ extraParams ++ actualParams)
  let defBody ← buildingTermWithDefaultχSpecialized baseParams (extraParams ++ actualParams) injectedBinders extractBody mod
  let cmd ← if attrs.isEmpty
    then `(command| def $(mkIdent extractedName):ident := $(defBody.body):term)
    else `(command| @[$[$attrs],*] def $(mkIdent extractedName):ident := $(defBody.body):term)
  elabVeilCommand cmd
  return defBody

-- NOTE: We only add `multiextracted` and `multiExtractSimp` attributes to
-- procedures. Ideally, we also need to add them to the internal mode
-- actions, but actions are not usually called in the internal mode,
-- and extracting them would double the time spent in extraction.

def specializeAndExtractInitializer (mod : Module) : CommandElabM Unit := do
  discard <| specializeAndExtractSingle injectedBinders extraDsimpsForSpecialize κ useWeak true mod ProcedureInfo.initializer (toExtName initializerName |> toExtractedName)

def specializeAndExtractInternalMode (mod : Module) : CommandElabM Unit := do
  let procs := mod.procedures.filter fun p => match p.info with | .procedure _ => true | _ => false
  for ps in procs do
    let attr1 ← `(Parser.Term.attrInstance| $(mkIdent `multiextracted):ident )
    -- let attr2 ← `(Parser.Term.attrInstance| multiExtractSimp ↓)
    discard <| specializeAndExtractSingle injectedBinders extraDsimpsForSpecialize κ useWeak false mod ps.info (attrs := #[attr1/-, attr2 -/])

/-- Extract each action into its own definition, returning them in `mod.actions`
order so the dispatcher can call each one the way its binders require. -/
def specializeAndExtractExternalActions (mod : Module) : CommandElabM (Array SpecializedTerm) :=
  mod.actions.mapM fun a => do
    let pi := a.info
    let extName := toExtName pi.name
    specializeAndExtractSingle injectedBinders extraDsimpsForSpecialize κ useWeak true mod pi
      (extractedName := toExtractedName extName) (toExtract := extName)

/-- Extract each action into its own definition and assemble `NextAct` as a
dispatcher over them.

Keeping every action in one definition made compilation superlinear in the
number of actions: LCNF's `simp` re-traverses the whole declaration on each of
its fixpoint iterations, and its cost per node grows with the declaration's
size. One definition per action turns that back into a sum of independent
costs. It also stops `#extract` from re-elaborating an action's body inside
`NextAct` after having already extracted it. -/
def specializeAndExtractActions (mod : Module) (extractedActions : Array SpecializedTerm) : CommandElabM Unit := do
  let lIdent := mkIdent `l
  let labelT ← mod.labelTypeStx
  let alts ← (mod.actions.zip extractedActions).mapM fun (a, extracted) => do
    let pi := a.info
    let (_, actualParams) ← mod.declarationAllParams pi.name (.procedure pi)
    let call ← extracted.callSyntax (mkIdent (toExtractedName (toExtName pi.name)))
    let args ← actualParams.mapM (·.arg)
    mkFunSyntax args call
  let finalBody ← do
    let multiExecType ← `(term| $(mkIdent ``VeilMultiExecM) ($κ) ExId $environmentTheory $environmentState $(mkIdent ``Unit))
    -- Need this annotation to avoid the `failed to elaborate eliminator, expected type is not available` error
    `(fun ($lIdent : $labelT) => (($lIdent.$(mkIdent `casesOn) $alts*) : $multiExecType))
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .actionLike actionNames)
  let defBody ← buildingTermWithDefaultχSpecialized baseParams extraParams injectedBinders finalBody mod
  let extractedName := toExtractedName assembledNextActName
  elabVeilCommand <| ←  `(command| def $(mkIdent extractedName):ident := $(defBody.body):term)

def specializeAndExtract : CommandElabM Unit := do
  let mod ← getCurrentModule
  specializeAndExtractInitializer injectedBinders extraDsimpsForSpecialize κ useWeak mod
  specializeAndExtractInternalMode injectedBinders extraDsimpsForSpecialize κ useWeak mod
  let extractedActions ← specializeAndExtractExternalActions injectedBinders extraDsimpsForSpecialize κ useWeak mod
  specializeAndExtractActions injectedBinders κ mod extractedActions

syntax (name := specializeAndExtractCmdStx) "#extract" ("!")? "log_entry_being" term
  ("dsimp_with " "[" ident,* "]")? (injectBindersStx)? : command

elab_rules : command
  | `(#extract $[!%$notUseWeakSign]? log_entry_being $logelem:term $[dsimp_with [$[$extraDsimps:ident],*]]? $[injection_begin $injectedBinders:bracketedBinder* injection_end]?) => do
    let extraDsimps := extraDsimps.getD #[]
    let injectedBinders := injectedBinders.getD #[]
    specializeAndExtract injectedBinders extraDsimps logelem notUseWeakSign.isNone

private def bindersToInjectForExecution [AddMessageContext m] [MonadOptions m] [MonadTrace m] [MonadEnv m]
    (mod : Veil.Module) : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let repConfigs ← resolveConcreteRepConfigs mod._concreteRepConfig
  let binders ← mod.assumeInstArgsWithConcreteRepConfig mod.mutableComponents repConfigs
    ConcreteRepConfig.domainLawfulFieldRepInstances ConcreteRepConfig.codomainLawfulFieldRepInstances
    #[``Repr, ``Enumeration] #[``Inhabited, ``DecidableEq] false
  -- Whether picks are logged is up to the caller: the model checker searches with the log off,
  -- and recovers traces with it on
  return binders.push (← `(bracketedBinder| [$(mkCIdent ``LogSwitch)]))

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
end FrontendExtraction

@[expose] section RuntimeExtraction

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

instance (priority := high) {α : Type u} (a : α) : Veil.Enumeration {x : α // Veil.eqWithoutSubst x a} where
  allValues := [⟨a, rfl⟩]
  complete := by rintro ⟨x, h⟩ ; simp [Veil.eqWithoutSubst] at h ; simp [h]

/- The rules below take the log instance as a parameter, as Loom's do, rather than fixing the one
   found here: extraction for the model checker uses the one under a `LogSwitch` (`Definitions.lean`),
   and Loom's lifted instance applies only where there is no switch. -/

section

variable {ρ σ} [inst4 : MonadPersistentLog Std.Format (VeilMultiExecM Std.Format ExId ρ σ)]

def ConstrainedExtractResult.pickSuchThat_VeilM (p : τ → Prop) [∀ x, Decidable (p x)] [instec : ExtCandidates Candidates Std.Format p] :
  ConstrainedExtractResult Std.Format (VeilExecM m ρ σ) (VeilMultiExecM Std.Format ExId ρ σ)
  (findOfCandidates _) (VeilM.pickSuchThat τ p) := ConstrainedExtractResult.pickList _ _ _ _ p (instec := instec)

def ConstrainedExtractResult.assume_VeilM {m} (p : Prop) [decp : Decidable p] :
  ConstrainedExtractResult Std.Format (VeilExecM m ρ σ) (VeilMultiExecM Std.Format ExId ρ σ)
  (findOfCandidates _) (@VeilM.assume m ρ σ p decp) := ConstrainedExtractResult.assume _ _ _ _ p (decp := decp)

def ConstrainedExtractResult.require_VeilM {m ex} (p : Prop) [decp : Decidable p] :
  ConstrainedExtractResult Std.Format (VeilExecM m ρ σ) (VeilMultiExecM Std.Format ExId ρ σ)
  (findOfCandidates _) (@VeilM.require m ρ σ p decp ex) :=
  match m with
  | .external => ConstrainedExtractResult.assume_VeilM p (decp := decp)
  | .internal => ConstrainedExtractResult.liftM _ _ _ _ (@VeilExecM.assert m ρ σ p decp ex)

end

/-- The computation without results: the empty choice. -/
@[inline]
def TsilT.empty {m : Type u → Type v} {α : Type u} : TsilT m α := []

/-- The failure branch of `assume` and `require` as extraction produces it
(`ConstrainedExtractResult.assume`) is the empty `TsilT` computation, lifted. If it's in the form
`MonadFlatMap'.op []`, the compiler cannot see that the branch has no results, since `op`
maps over the list at every layer of the monad; so the bind that follows, together with the
rest of the action, stays compiled into the most common path of the model checker. -/
@[multiExtractSimp] theorem VeilMultiExecM.op_nil :
    (MonadFlatMap'.op ([] : List (VeilMultiExecM κ ε ρ σ α)) : VeilMultiExecM κ ε ρ σ α)
      = liftM (TsilT.empty : TsilT (PeDivM (List κ)) α) := rfl

/-! ### Pre-simplified continuation-facing primitives

Extraction leaves an action as a chain of `bind`s in `VeilMultiExecM`, one per statement. For the
deterministic ones (`get`, `read`, `modifyGet`, `pure`, a pick candidate's `log; pure`), the rules
below rewrite the `bind` into a definitionally equal form that applies the continuation directly,
e.g. `go get >>= k` into `getThen k`. They are `rfl` thanks to the `LogMonoid.isEmpty` fast path
in Loom's `bind`.

The compiler does not get there by itself: `cse` runs before `simp` and merges all the
`MonadFlatMapGo.go … get` of an action into one local function, which is never inlined (used
several times, larger than `compiler.small`), so every read, used or not, costs a closure call,
five allocations and `match`es on the result list, log, `DivM` and `Except`. Hence one rule per
primitive: the generic `go x >>= k = fun r s => match x r s with …` is `rfl` too, but keeps `x`
for `cse` to share.

`getThen` and the like are not unfolded in the term: `simp` would beta-reduce the over-applied `k`
with `betaRev (useZeta := true)`, inlining a `let`-bound join point at its head once per jump, the
growth `ConstrainedExtractResult.joinPoint` exists to prevent. The compiler unfolds them in ANF,
where beta does not duplicate.

The `IsSubStateOf` and `IsSubReaderOf` assumptions are those of the actions themselves: their
`get`, `read` and `modifyGet` are elaborated through Veil's sub-state and sub-reader instances
(`SubState.lean`), `dsimp` matches the left-hand sides syntactically, and `getFrom`, `setIn` and
`readFrom` come from the same classes. `VeilExecM` fixes its exception type to `ExId`, so the
`go` rules do too. -/

section PreSimplifiedContinuationFacingPrimitives

namespace VeilMultiExecM

variable {κ ε ρ σ τ ρ' α β : Type} {mode : Mode}

/-- `go get >>= k`, run directly: the continuation receives the current sub-state. -/
@[always_inline, inline]
def getThen [IsSubStateOf τ σ] (k : τ → VeilMultiExecM κ ε ρ σ α) :
    VeilMultiExecM κ ε ρ σ α :=
  fun r s => k (getFrom s) r s

/-- `go read >>= k`, run directly: the continuation receives the theory. -/
@[always_inline, inline]
def readThen [IsSubReaderOf ρ' ρ] (k : ρ' → VeilMultiExecM κ ε ρ σ α) :
    VeilMultiExecM κ ε ρ σ α :=
  fun r s => k (readFrom r) r s

/-- `go (modifyGet f) >>= k`, run directly: the continuation runs on the updated state. -/
@[always_inline, inline]
def modifyGetThen [IsSubStateOf τ σ] (f : τ → β × τ)
    (k : β → VeilMultiExecM κ ε ρ σ α) : VeilMultiExecM κ ε ρ σ α :=
  fun r s => match f (getFrom s) with
    | (a, x') => k a r (setIn x' s)

@[multiExtractSimp] theorem go_get_bind [IsSubStateOf τ σ]
    (k : τ → VeilMultiExecM κ ExId ρ σ α) :
    (MonadFlatMapGo.go (m := VeilExecM mode ρ σ) (n := VeilMultiExecM κ ExId ρ σ)
        (MonadStateOf.get : VeilExecM mode ρ σ τ) >>= k)
      = getThen k := rfl

@[multiExtractSimp] theorem go_read_bind [IsSubReaderOf ρ' ρ]
    (k : ρ' → VeilMultiExecM κ ExId ρ σ α) :
    (MonadFlatMapGo.go (m := VeilExecM mode ρ σ) (n := VeilMultiExecM κ ExId ρ σ)
        (MonadReader.read : VeilExecM mode ρ σ ρ') >>= k)
      = readThen k := rfl

@[multiExtractSimp] theorem go_modifyGet_bind [IsSubStateOf τ σ]
    (f : τ → β × τ) (k : β → VeilMultiExecM κ ExId ρ σ α) :
    (MonadFlatMapGo.go (m := VeilExecM mode ρ σ) (n := VeilMultiExecM κ ExId ρ σ)
        (MonadState.modifyGet f : VeilExecM mode ρ σ β) >>= k)
      = modifyGetThen f k := rfl

/-- A state read whose result is unused (the frontend reopens the state after every statement)
is no read at all. The pattern `fun _ => k` only unifies with a continuation that does not
depend on its binder. -/
@[multiExtractSimp] theorem getThen_const [IsSubStateOf τ σ]
    (k : VeilMultiExecM κ ε ρ σ α) : getThen (τ := τ) (fun _ => k) = k := rfl

@[multiExtractSimp] theorem readThen_const [IsSubReaderOf ρ' ρ]
    (k : VeilMultiExecM κ ε ρ σ α) : readThen (ρ' := ρ') (fun _ => k) = k := rfl

-- Using `let` to avoid duplicating the expression in `k`
@[multiExtractSimp] theorem pure_bind (x : β) (k : β → VeilMultiExecM κ ε ρ σ α) :
    ((pure x : VeilMultiExecM κ ε ρ σ β) >>= k) = (let y := x ; k y) := rfl

/-- A pick's per-candidate computation: log the candidate, then return it.

Only for Loom's log instance, which always logs. Under a `LogSwitch` the log is
`if sw.enabled then [w] else []`: whether it is empty depends on the switch, which is unknown
here, so the `bind` does not reduce and there is no `rfl` form. The `bind` then stays in the
extracted term, and the compiler inlines it: what it compiles to is the result above with the
switch tested at run time, `[(if sw.enabled then [w] else [], DivM.res (Except.ok x, s))]`, with
`w` only computed when the switch is on. -/
@[multiExtractSimp] theorem log_bind_pure (w : κ) (x : β) :
    ((MonadPersistentLog.log w : VeilMultiExecM κ ε ρ σ PUnit) >>= fun _ => pure x)
      = fun _ s => [([w], DivM.res (Except.ok x, s))] := rfl

end VeilMultiExecM

end PreSimplifiedContinuationFacingPrimitives

/-! ### Binds of picks and the trailing `pure ()`

Two binds survive the rewrites above, because their left-hand side has no statically known
results: a pick followed by its continuation, and the `pure ()` that `VeilM.returnUnit` puts
after every action. Loom's generic rule would extract a pick as `MonadFlatMap'.op` over one
computation per candidate, and the `bind` after it would collect their results into a list,
then take it apart again with a runtime `match` on its length; the trailing bind would then run
over the whole action's results once more. Loom's rules for these two shapes avoid both:

- A pick followed by `f` (`ConstrainedExtractResult.pickList_bind`, `pick_bind`) becomes
  `MonadFlatMap'.opMap candidates fun x => log (rep x) >>= fun _ => f' x`. On `VeilMultiExecM`,
  `opMap` passes the theory and the state down to `TsilT`, where it is one `List.flatMap` over
  the candidates, and each candidate's `bind` compiles to prefixing its log entry to the
  results of `f' x` (of which there are none, most often, when a `require` fails), or to nothing
  when the log is off (`LogSwitch`).
- `act >>= fun _ => pure ()` becomes `act'` itself (`bind_pure_unit`).

They are registered with a high priority (below), so that `extract_list_use_extracted` tries
them before the generic `bind`, which matches the same goals. -/

section PicksAndTrailingPure

variable {ρ σ τ β : Type} {mode : Mode} [inst4 : MonadPersistentLog Std.Format (VeilMultiExecM Std.Format ExId ρ σ)]

open MultiExtractor

/-- `ConstrainedExtractResult.pickList_bind` for `VeilM.pickSuchThat`, which the discrimination
tree does not see through (see `pickSuchThat_VeilM`). -/
def ConstrainedExtractResult.pickSuchThat_bind_VeilM (p : τ → Prop) [∀ x, Decidable (p x)]
    [instec : ExtCandidates Candidates Std.Format p] {f : τ → VeilM mode ρ σ β}
    (hf : ∀ x, ConstrainedExtractResult Std.Format (VeilExecM mode ρ σ)
      (VeilMultiExecM Std.Format ExId ρ σ) (findOfCandidates _) (f x)) :
    ConstrainedExtractResult Std.Format (VeilExecM mode ρ σ) (VeilMultiExecM Std.Format ExId ρ σ)
      (findOfCandidates _) (VeilM.pickSuchThat τ p >>= f) :=
  ConstrainedExtractResult.pickList_bind _ _ _ _ p (instec := instec) hf

end PicksAndTrailingPure

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
/- These match goals that `ConstrainedExtractResult.bind` matches too, and must be tried first.
   The key of `bind_pure_unit` has the continuation as a lambda, which the discrimination tree
   does not index, so it is tried (and fails to unify) on the other binds of `PUnit` as well. -/
attribute [multiextracted high] ConstrainedExtractResult.bind_pure
  ConstrainedExtractResult.bind_pure_unit
  ConstrainedExtractResult.pick_bind
  ConstrainedExtractResult.pickSuchThat_bind_VeilM

open MultiExtractor in
attribute [multiExtractSimp]
  /- Run after the operand has been simplified, and only in extraction's simpset.
     `dsimproc_decl` itself does not register this with ordinary `dsimp`. -/
  simpExtractedValueLet

open MultiExtractor in
attribute [multiExtractSimp ↓] ConstrainedExtractResult.pure
  ConstrainedExtractResult.bind ConstrainedExtractResult.assume
  ConstrainedExtractResult.filterAuxM
  ConstrainedExtractResult.pick
  -- findOfCandidates Candidates.find ExtCandidates.rep ExtCandidates.core
  -- instEnumerationEqWithoutSubst
  ConstrainedExtractResult.pickList ConstrainedExtractResult.liftM ConstrainedExtractResult.ite
  ConstrainedExtractResult.val
  ConstrainedExtractResult.pickSuchThat_VeilM
  ConstrainedExtractResult.assume_VeilM
  ConstrainedExtractResult.require_VeilM
  ConstrainedExtractResult.pickList_bind ConstrainedExtractResult.pick_bind
  ConstrainedExtractResult.pickSuchThat_bind_VeilM
  ConstrainedExtractResult.bind_pure ConstrainedExtractResult.bind_pure_unit
  /- `change` wraps the new extraction goal in `id` as a type checkpoint. Expose
     its let-bound result so the projection simproc can remove the certificate. -/
  id

/-- Extract the execution result from a DivM-wrapped result. Unlike `getPostState`
which only returns `Option σ`, this preserves the return value of a successful
execution as well as information about assertion failures, both of which can be
used as counter-examples by the model checker. -/
@[inline]
def getExecutionResult (c : DivM ((Except ε α) × σ)) : Veil.ExecutionResult ε σ α :=
  match c with
  | .res ((.ok a, st)) => .success a st
  | .res ((.error e, st)) => .assertionFailure e st
  | .div => .divergence

/-- Extract the resulting post-state from a DivM-wrapped result pair. The
semantics of exceptions in Veil is that the whole computation is reverted, so
there is no post-state in the `error` case. -/
@[inline]
def getPostState (c : DivM ((Except ε α) × σ)) : Option σ :=
  getExecutionResult c |>.toPostState

def getAllPostStates (c : List (DivM ((Except ε α) × σ))) : List (Option σ) :=
  c.map getPostState

/-- Extract all valid states from a VeilMultiExecM computation -/
def extractValidStates (exec : Veil.VeilMultiExecM κᵣ Int ρ σ Unit) (rd : ρ) (st : σ) : List (Option σ) :=
  exec rd st |>.map Prod.snd |> getAllPostStates

/-- The transitions of all labels, in label order, built in one pass and already split into the
successful ones and the assertion failures, which is how the model checker consumes them
(`EnumerableTransitionSystem.tr`). `next` is specialized in, so there is no closure per label, and
only the results that exist are allocated: no intermediate `(label, outcome)` list, no partition
afterwards. The model checker runs this on every state, and most labels fail their `require`, so
the per-label cost matters more than the per-result cost.

The labels are traversed last to first and each label's results are pushed in front of `acc`,
which keeps the loop tail recursive and the order unchanged; the caller passes the reversed label
list, computed once rather than per state. -/
@[specialize]
def transitionsOfLabelsRev (next : κ → Veil.VeilMultiExecM κᵣ Int ρ σ Unit) (rd : ρ) (st : σ) :
    List κ → Veil.Transitions κ Int σ → Veil.Transitions κ Int σ
  | [], acc => acc
  | l :: ls, acc =>
    match next l rd st with
    -- the usual case: `require` failed
    | [] => transitionsOfLabelsRev next rd st ls acc
    -- a deterministic step
    | [(_, r)] => transitionsOfLabelsRev next rd st ls (prependResult l r acc)
    | rs => transitionsOfLabelsRev next rd st ls (prependResults l rs acc)
where
  /-- One result in front of the transitions. -/
  @[inline] prependResult (l : κ) (r : DivM ((Except Int Unit) × σ)) (acc : Veil.Transitions κ Int σ) :
      Veil.Transitions κ Int σ :=
    match r with
    | .res (.ok _, s) => { acc with successes := (l, s) :: acc.successes }
    | .res (.error e, s) => { acc with failures := ⟨l, e, s⟩ :: acc.failures }
    | .div => acc
  /-- Several results (a pick) in front of the transitions, in their order, with one allocation per
  result; `map` and `++` would cost four (`map` compiles to `mapTR`, `++` to `appendTR`). Only
  labels with two or more results get here. -/
  prependResults (l : κ) : List (List κᵣ × DivM ((Except Int Unit) × σ)) → Veil.Transitions κ Int σ →
      Veil.Transitions κ Int σ
    | [], acc => acc
    | (_, r) :: rs, acc => prependResult l r (prependResults l rs acc)

/-- Extract all execution results, preserving successful return values. -/
def extractAllResults (exec : Veil.VeilMultiExecM κᵣ ε ρ σ α) (rd : ρ) (st : σ) : List (ExecutionResult ε σ α) :=
  exec rd st |>.map fun (_, st) => getExecutionResult st

end RuntimeExtraction

meta def Module.assembleEnumerableTransitionSystem [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [AddErrorMessageContext m] [MonadTrace m] [MonadEnv m] [MonadOptions m] [AddMessageContext m] (mod : Module) : m Command := do
  mod.throwIfAlreadyDeclared enumerableTransitionSystemName

  -- Step 1: Use mkDerivedDefinitionsParamsMapFn pattern (like specializeActionsCore)
  let actionNames := Std.HashSet.ofArray $ mod.actions.map (·.name)
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) (.derivedDefinition .actionLike actionNames)

  -- HACK: filter out `ρ`, `σ`, `IsSubStateOf` and `IsSubReaderOf` from `baseParams`
  -- ... and put them at the beginning of `extraParams` instead
  let (baseParams, others) := baseParams.partition fun p => !(p.kind matches .environmentState | .backgroundTheory | .moduleTypeclass .environmentState | .moduleTypeclass .backgroundTheory)
  let theoryStx ← mod.theoryStx
  let stateStx ← mod.stateStx
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
    let fieldConcrete ← `($fieldConcreteDispatcher $(← mod.uninterpretedParamIdents)*)
    let stateStx ← `($stateIdent $fieldConcrete)
    let labelStx ← mod.labelTypeStx
    let (CInit, CNext) := (mkVeilImplementationDetailIdent `CInit, mkVeilImplementationDetailIdent `CNext)
    let (th, st) := (mkVeilImplementationDetailIdent `th, mkVeilImplementationDetailIdent `st)
    let lbls := mkVeilImplementationDetailIdent `lbls
    let filterMap ← `($(mkIdent ``List.filterMap) $(mkIdent ``id))

    -- NOTE: Use the `ext` version of `initializer` below!!!
    `({
      $(mkIdent `initStates):ident :=
        let $CInit := $(mkIdent <| toExtractedName <| toExtName initializerName) $theoryStx $stateStx $(← mod.uninterpretedParamIdents)*
        $(mkIdent ``extractValidStates) $CInit $theoryId $(mkIdent ``default) |> $filterMap
      $(mkIdent `tr):ident := let $lbls := $(mkIdent ``List.reverse) (@$(mkIdent ``Veil.Enumeration.allValues) _ $labelsId) ; fun $th $st =>
        let $CNext := $(mkIdent <| toExtractedName assembledNextActName) $theoryStx $stateStx $(← mod.uninterpretedParamIdents)*
        $(mkIdent ``transitionsOfLabelsRev) $CNext $th $st $lbls ⟨[], []⟩
      : $(mkIdent ``Veil.EnumerableTransitionSystem)
        $theoryStx ($(mkIdent ``List) $theoryStx)
        $stateStx ($(mkIdent ``List) $stateStx)
        $(mkIdent ``Int)
        $labelStx ($(mkIdent ``Veil.Transitions) $labelStx $(mkIdent ``Int) $stateStx)
        $theoryId
     })

  -- Step 4: Specialize `χ`, `χ_rep`, `χ_rep_lawful` and build the term
  let enumerableTransitionSystemTerm ← buildingTermWithDefaultχSpecialized baseParams (others ++ extraParams)
    injectedBinders finalBody mod specializeToOther

  -- Step 5: Add @[specialize] attribute
  `(command| @[inline] def $enumerableTransitionSystem:ident := $(enumerableTransitionSystemTerm.body))

end Veil.Extract
