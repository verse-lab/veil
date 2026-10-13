module

public meta import Veil.Frontend.DSL.Module.Elaborators.Verification

public meta section

open Lean Parser Elab Command Term
namespace Veil

-- NOTE: `temporal` refers to `Init` and `Next` which are only available
-- after the spec is finalized
@[command_elab Veil.temporalDeclaration]
def elabTemporalDeclaration : CommandElab := fun stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot declare a temporal property outside of a Veil module!")
  mod ← mod.ensureStateIsDefined
  -- Needs `Init`, `NextStep`, …, which `#gen_spec` leaves to the first verification
  -- command under `veil.deferVCGeneration`.
  mod ← mod.ensureVerificationSpec stx
  let (name, prop) ← match stx with
    | `(command|temporal $[$name:propertyName]? $prop:tlfml) =>
      pure (name.elim (Name.mkSimple s!"temporal_{mod.temporalProperties.size}") (·.getPropertyName), prop)
    | _ => throwUnsupportedSyntax
  mod.throwIfAlreadyDeclared name
  -- Include the dependencies of both the formula bindings and its proof obligation.
  let ghostDefs := mod._derivedDefinitions.valuesArray.filter fun dd =>
      match dd.kind with | .ghost _ | .theoryGhost _ => true | _ => false
  let dependencies := (Std.HashSet.ofArray (mod.actions.map (·.name)))
    |>.union (Std.HashSet.ofArray (ghostDefs.map (·.name)))
    |>.union (Std.HashSet.ofArray #[assembledInitName, assembledNextStepName,
        assembledInvariantsName, assembledAssumptionsName])
  let dk : DeclarationKind := .derivedDefinition .actionLike dependencies
  let (baseParams, extraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·) dk
  let lp : TemporalProperty := { name := name, extraParams := extraParams, term := prop, userSyntax := stx }
  let baseBinders ← baseParams.mapM (·.binder)
  let extraBinders ← extraParams.mapM (·.binder)
  let allBinders := (← baseBinders.mapM mkImplicitBinder) ++ (← extraBinders.mapM mkImplicitBinder)
  -- Build let bindings for each action's transition relation
  -- For action `send (x : ts)`, generate:
  --   let send := fun x => @send.ext.tr <modArgs> x th
  -- For action `poll` (no params), generate:
  --   let poll := @poll.ext.tr <modArgs> th
  let thIdent := mkVeilImplementationDetailIdent `th
  let mut letBindings : Array (Ident × Term) := #[]
  for act in mod.actions do
    let actTrName := mkIdent <| toTransitionName <| toExtName act.name
    let ((_, modArgs), (specificBinders, specificArgs)) ← mod.declarationSplitBindersArgs act.name act.info.declarationKind
    let specificFunBinders ← specificBinders.mapM bracketedBinderToFunBinder
    let appTerm ← `(@$actTrName $modArgs* $specificArgs* $thIdent)
    let rhs ← mkFunSyntax specificFunBinders appTerm
    letBindings := letBindings.push (mkIdent act.name, rhs)
  -- Build let bindings for mutable relation fields, so `⌜ r x ⌝` works like
  -- a state predicate.
  -- NOTE: Another consideration could be to override `⌜ ... ⌝` so it expands
  -- into `⌜ fun st => State.casesOn (getFrom st) ... ⌝`, but that might not
  -- delaborate nicely. So here the approach is much more restrictive.
  for sc in mod.mutableComponents do
    if sc.kind == .relation then
      let stIdent := mkVeilImplementationDetailIdent `st
      let stBinder ← `(Lean.Parser.Term.funBinder| ($stIdent : $environmentState))
      let argIdents := sc.domainTerms.mapIdx fun i _ =>
        mkIdent <| mkVeilImplementationDetailName (.mkSimple s!"arg{i}")
      let argBinders ← sc.domainTerms.mapIdxM fun i dom =>
        `(Lean.Parser.Term.funBinder| ($(argIdents[i]!) : $dom))
      let core ← `(($(mkIdent ``getFrom) $stIdent).$(mkIdent sc.name))
      let field ← `(term| (($fieldRepresentation _).$(mkIdent `get) $core))
      let app := Syntax.mkApp field argIdents
      let rhs ← mkFunSyntax (argBinders.push stBinder) $ ← `(term| @$(mkIdent ``Eq) $(mkIdent ``Bool) $app $(mkIdent ``true))
      letBindings := letBindings.push (mkIdent sc.name, rhs)
  -- Build let bindings for each ghost definition
  -- For ghost `sent (x : ts)` (state-dependent), generate:
  --   let sent := fun x st => @sent <modArgs> x th st
  -- For theory-only ghosts, generate:
  --   let gname := @gname <modArgs> th
  for gdef in ghostDefs do
    let ghostRef := mkIdent gdef.name
    let (baseParams, extraParams, actualParams) ← mod.declarationSplitParams gdef.name gdef.declarationKind
    let userParams := actualParams.filter fun p => p.kind != .theoryArg && p.kind != .stateArg
    let specificFunBinders ← userParams.mapM fun p => p.binder >>= bracketedBinderToFunBinder
    -- Ghost definitions take user arguments before extracted Decidable instances.
    let args ← (baseParams ++ userParams ++ extraParams).mapM (·.arg)
    let (specificFunBinders, body) ← if gdef.kind matches .ghost _ then
      let stIdent := mkVeilImplementationDetailIdent `st
      let stBinder : TSyntax `Lean.Parser.Term.funBinder := stIdent
      let body ← `(@$ghostRef $args* $thIdent $stIdent)
      pure (specificFunBinders.push stBinder, body)
    else
      let body ← `(@$ghostRef $args* $thIdent)
      pure (specificFunBinders, body)
    let rhs ← mkFunSyntax specificFunBinders body
    letBindings := letBindings.push (mkIdent gdef.name, rhs)
  -- Assemble the body: let bindings + [tlfml| user_formula ]
  let fullBody ← do
    let body ← letBindings.foldrM (init := ← `([tlfml| $prop])) fun (bindName, bindVal) body =>
      `(let $bindName := $bindVal; $body)
    -- Expose immutable theory fields in temporal formulas, matching assertions and ghosts.
    let temporalPredType ← `($(mkIdent ``Lentil.pred) $environmentState)
    let bodyWithTheory ← liftTermElabM <|
      mod.withTheoryAndStateTermTemplate
        [(.theory, thIdent, true)]
        (some temporalPredType)
        (fun _ _ => pure body)
    `(fun ($thIdent : $environmentTheory) => $bodyWithTheory)
  -- Generate the definition
  -- NOTE: We might use `remove_unused_args%` to trim some unused arguments, but
  -- that makes the later use of the temporal property in proofs more complicated,
  -- as we need to figure out which arguments got removed in building its syntax of application
  let cmd ← `(noncomputable def $(mkIdent name) $[$allBinders]* := $fullBody)
  elabVeilCommand cmd
  let newMod := { mod with
    temporalProperties := mod.temporalProperties.push lp,
    _declarations := mod._declarations.insert name .temporalProperty
  }
  localEnv.modifyModule (fun _ => newMod)

private def Module.getStatementForTemporalTheorems [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [AddErrorMessageContext m]
  (mod : Module) (propName : Name) : m (Name × Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Term) := do
  unless mod.temporalProperties.any (·.name == propName) do
    throwError s!"No temporal property named '{propName}' declared in module {mod.name}"
  -- Build the proof obligation:
  --   ∀ (sorts...) (typeclasses...) (th : Theory),
  --     rts.assumptions th →
  --     pred_implies (systemBehavior rts th) (<propName> th)
  -- Use the same binders as the temporal definition.
  let (allModParams, _) ← mod.declarationAllParams propName .temporalProperty
  let allBinders ← allModParams.mapM fun p => p.binder >>= mkImplicitBinder
  -- Build the syntax of the theorem
  let thId := mkIdent `th
  let thBinder ← `(bracketedBinder| ($thId : $environmentTheory))
  -- Construct the behavior predicate directly using Init and Next
  -- (avoiding relationalTransitionSystem which restricts ρ/σ to concrete types)
  -- behavior = ⌜ Init th ⌝ ∧ □ ⟨ NextStep th ⟩ ∧ □ ⌜ Invariants th ⌝
  -- Get the module-level args for Init and NextStep
  let initRef ← do
    let ((_, initModArgs), _) ← mod.declarationSplitBindersArgs assembledInitName
      (mod._derivedDefinitions[assembledInitName]!.declarationKind)
    `(@$assembledInit $initModArgs* $thId)
  let nextStepRef ← do
    let ((_, nextStepModArgs), _) ← mod.declarationSplitBindersArgs assembledNextStepName
      (mod._derivedDefinitions[assembledNextStepName]!.declarationKind)
    `(@$assembledNextStep $nextStepModArgs* $thId)
  -- Also include □⌜Invariants⌝ so the user can use safety invariants in liveness proofs
  let invRef ← do
    let ((_, invModArgs), _) ← mod.declarationSplitBindersArgs assembledInvariantsName
      (mod._derivedDefinitions[assembledInvariantsName]!.declarationKind)
    `(@$assembledInvariants $invModArgs* $thId)
  let behavior ← `([tlfml| ⌜ $initRef ⌝ ∧ □ ⟨ $nextStepRef ⟩ ∧ □ ⌜ $invRef ⌝ ])
  let hassBinder ← do
    let hassId := mkIdent `hass
    -- Assumptions also has module params; pass them explicitly
    let ((_, assumpModArgs), _) ← mod.declarationSplitBindersArgs assembledAssumptionsName
      (mod._derivedDefinitions[assembledAssumptionsName]!.declarationKind)
    `(bracketedBinder| ($hassId : @$assembledAssumptions $assumpModArgs* $thId))
  let propRef ← do
    let allArgs ← allModParams.mapM (·.arg)
    `(@$(mkIdent propName) $allArgs* $thId)
  let thmName := propName ++ `_proof
  let thmType ← `($(mkIdent `Lentil.pred_implies) $behavior $propRef)
  pure (thmName, allBinders ++ #[thBinder, hassBinder], thmType)

-- FIXME: This `incremental` does not work as intended; even changing it into a simpler
-- `Macro`-based implementation we cannot achieve full incrementality (e.g., the incrementality
-- breaks at a call to `split_ands`).
@[incremental, command_elab Veil.proveTemporalBy]
def elabProveTemporalBy : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "prove_temporal_by must be inside a Veil module!")
  let mod ← mod.ensureVerificationSpec stx
  let (propName, tacs) ← match stx with
    | `(command|prove_temporal_by [$name:ident] $tacs:tacticSeq) => pure (name.getId.eraseMacroScopes, tacs)
    | _ => throwUnsupportedSyntax
  let (thmName, allBinders, thmType) ← mod.getStatementForTemporalTheorems propName
  let thmCmd ← `(command|
    theorem $(mkIdent thmName) $[$allBinders]* : $thmType := by $tacs)
  elabVeilCommand thmCmd

open Term in
@[term_elab kw_fetch_temporal_theorem_body]
def elabFetchTemporalTheoremBody : TermElab := fun stx expectedType => do
  let mod ← getCurrentModule (errMsg := "temporal_theorem_body_of% must be inside a Veil module!")
  mod.throwIfSpecNotFinalized
  let propName ← match stx with
    | `(temporal_theorem_body_of% $i:ident) => pure i.getId.eraseMacroScopes
    | _ => throwUnsupportedSyntax
  let (_, allBinders, thmType) ← mod.getStatementForTemporalTheorems propName
  let final ← `(∀ $[$allBinders]*, $thmType)
  elabTerm final expectedType

end Veil
