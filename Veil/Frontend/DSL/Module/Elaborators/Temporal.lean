module

public meta import Veil.Frontend.DSL.Module.Elaborators.Verification

public meta section

open Lean Parser Elab Command Term
namespace Veil

/-! ## State atoms of temporal formulas

Lentil reads `⌜ t ⌝` as `state_pred t` with `t : σ → Prop`. While Veil elaborates a temporal property of a
module (`veil.temporal.moduleAtoms`), `t` is instead a proposition over the module's fields, as in an
assertion: the theory fields are bound around the whole formula, and the state fields around each atom. -/

/-- Internal: the atom `⌜ t ⌝` of a `[tlfml| …]` formula, see `elabTlfmlStateAtom`. -/
syntax (name := tlfmlStateAtom) "veil_tlfml_state_atom% " term:max : term

macro_rules
  | `([tlfml| ⌜ $t:term ⌝]) => `(veil_tlfml_state_atom% ($t))
  -- These name the action labels that the model checker sees, which a `Lentil.pred` cannot observe
  | `([tlfml| E($a:ident $_args*)]) => Macro.throwErrorAt a
    "`E(…)` is an atom of `liveness` properties, which are model checked; a `temporal` property cannot use it"
  | `([tlfml| T($a:ident $_args*)]) => Macro.throwErrorAt a
    "`T(…)` is an atom of `liveness` properties, which are model checked; a `temporal` property cannot use it"

/-- `⌜ t ⌝` as Lentil reads it, `state_pred t`, or, while a temporal property of the current module is
elaborated, `state_pred (fun st => t)` with the state fields bound in `t` as in an assertion. -/
@[term_elab tlfmlStateAtom] def elabTlfmlStateAtom : TermElab := fun stx expectedType? => do
  let `(veil_tlfml_state_atom% $t) := stx | throwUnsupportedSyntax
  unless veil.temporal.moduleAtoms.get (← getOptions) do
    return ← elabTerm (← `($(mkIdent ``Lentil.state_pred) $t)) expectedType?
  let mod ← getCurrentModule
  let st := mkVeilImplementationDetailIdent `st
  let body ← mod.withTheoryAndStateTermTemplate [(.state .none "_conc", st, true)] (some (← `(Prop)))
    (fun _ _ => `(uqc% ($t:term)))
  elabTerm (← `($(mkIdent ``Lentil.state_pred) fun ($st : $environmentState) => $body)) expectedType?

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
      pure (name.elim (Name.mkSimple s!"temporal_{mod.verifiableTemporalProperties.size}") (·.getPropertyName), prop)
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
  let lp : TemporalProperty :=
    { name := name, formula := prop, target := .verify, extraParams := extraParams, userSyntax := stx }
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
  -- State fields and ghosts need no bindings: each `⌜ t ⌝` sees them as an assertion does
  -- (`elabTlfmlStateAtom`).
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
  -- The atoms are read against this module (`elabTlfmlStateAtom`)
  withScope (fun scope => { scope with opts := veil.temporal.moduleAtoms.set scope.opts true }) do
    elabVeilCommand cmd
  let newMod := { mod with
    temporalProperties := mod.temporalProperties.push lp,
    _declarations := mod._declarations.insert name .temporalProperty
  }
  localEnv.modifyModule (fun _ => newMod)

private def Module.getStatementForTemporalTheorems [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [AddErrorMessageContext m]
  (mod : Module) (propName : Name) : m (Name × Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Term) := do
  unless mod.verifiableTemporalProperties.any (·.name == propName) do
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
