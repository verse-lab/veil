module

public meta import Veil.Frontend.DSL.Module.Elaborators.Verification
public meta import Lentil

public meta section

open Lean Parser Elab Command Term
namespace Veil

/-- Declare a temporal property for proving, model checking, or both. -/
@[command_elab Veil.temporalDeclaration]
def elabTemporalDeclaration : CommandElab := fun stx => do
  let mut mod ← getCurrentModule (errMsg := "You cannot declare a temporal property outside of a Veil module!")
  mod ← mod.ensureStateIsDefined
  let (only?, name?, formula) ← match stx with
    | `(command|temporal $[(only := $t:ident)]? $[$name:propertyName]? $f:tlfml) => pure (t, name, f)
    | _ => throwUnsupportedSyntax
  let target ← match only? with
    | none => pure TemporalTarget.both
    | some t => match t.getId with
      | `verify => pure .verify
      | `check => pure .check
      | _ => throwErrorAt t "expected `verify` (only prove the property) or `check` (only model check it)"
  let name := name?.elim (Name.mkSimple s!"temporal_{mod.temporalProperties.size}") (·.getPropertyName)
  mod.throwIfAlreadyDeclared name
  let tp : TemporalProperty :=
    { name, formula, target, userSyntax := stx,
      checkPending := target.needsCheck,
      verifyPending := target.needsVerify }
  mod := { mod with
    temporalProperties := mod.temporalProperties.push tp
    _declarations := mod._declarations.insert name .temporalProperty }
  if mod.isSpecFinalized then
    if tp.checkPending then
      mod ← mod.generateTemporalDefinition tp .check
    localEnv.modifyModule (fun _ => mod)
    if tp.verifyPending then
      mod ← mod.ensureVerificationSpec stx
  localEnv.modifyModule (fun _ => mod)

private def Module.getStatementForTemporalTheorems [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [AddErrorMessageContext m]
  (mod : Module) (propName : Name) : m (Name × Array (TSyntax `Lean.Parser.Term.bracketedBinder) × Term) := do
  unless mod.verifiableTemporalProperties.any (·.name == propName) do
    if mod.temporalProperties.any (·.name == propName) then
      throwError s!"Temporal property '{propName}' is only model checked, so it has nothing to prove"
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

/-- Generate the theorem `<p>._proof`. Its proof starts with the prelude
`tstart hInit hNext hInv` and `tdsimp only [p]`, followed by the user's tactics. As for
`elabProveVeilInvariantGoal`, `@[incremental]` keeps the command's snapshot bundle
available for Lean's theorem/tactic elaborators, and the generated syntax stays the
same across proof edits, so that they reuse the prelude and the unchanged prefix of
the proof. -/
@[command_elab Veil.proveTemporalBy, incremental]
def elabProveTemporalBy : CommandElab := fun stx => do
  let (name, rbrack, tacs) ← match stx with
    | `(command|prove_temporal_by [$name:ident]%$rbrack $tacs:tacticSeq) => pure (name, rbrack, tacs)
    | _ => throwUnsupportedSyntax
  let mod ← getCurrentModule (errMsg := "prove_temporal_by must be inside a Veil module!")
  let propName := name.getId.eraseMacroScopes
  -- Key quotation hygiene by the property. The default seed includes the whole
  -- command's text, so editing a tactic would change generated names.
  withInitQuotContext (some (hash (← getCurrNamespace, propName))) do
    -- Anchor generated syntax to the property name: the whole command's end
    -- position moves on proof edits. The user's tactics retain their own positions.
    withRef name do
      -- Hide the snapshot bundle from the helper declarations of deferred
      -- preparation; see `elabProveVeilInvariantGoal`.
      let mod ← withReader (fun ctx => { ctx with snap? := none }) <|
        mod.ensureVerificationSpec name
      let (thmName, allBinders, thmType) ← mod.getStatementForTemporalTheorems propName
      -- The end of the header, `]`, should show the goal after the prelude.
      let entry : TSyntax `tactic := ⟨(← `(tactic| skip)).raw.setInfo rbrack.getHeadInfo⟩
      let steps := tacticSeqSteps tacs
      -- The prelude names the conjuncts `⌜ Init ⌝`, `□ ⟨ NextStep ⟩` and `□ ⌜ Invariants ⌝`
      -- of the behavior, for the user's tactics to refer to, and unfolds the property.
      let cmd ← `(command|
        theorem $(mkIdent thmName) $[$allBinders]* : $thmType := by
          tstart $(mkIdent `hInit) $(mkIdent `hNext) $(mkIdent `hInv)
          tdsimp only [$(mkIdent propName):ident]
          $entry:tactic
          $steps;*)
      -- Delegate directly to Lean's theorem/tactic elaborators, which reuse the
      -- snapshots of the prelude and of the unchanged tactics.
      elabCommand cmd

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
