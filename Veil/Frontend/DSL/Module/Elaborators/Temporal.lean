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
  | `([tlfml| E($a:ident $_args*)]) => Macro.throwErrorAt a "`E(…)` only exists for model checking"
  | `([tlfml| T($a:ident $_args*)]) => Macro.throwErrorAt a "`T(…)` only exists for model checking"
  | `([tlfml| WF($a:ident $_args*)]) => Macro.throwErrorAt a "`WF(…)` only exists for model checking"
  | `([tlfml| SF($a:ident $_args*)]) => Macro.throwErrorAt a "`SF(…)` only exists for model checking"

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

/-- Declares a temporal property. Its definitions (`Module.defineTemporalCheck` and
`Module.defineTemporalVerify`) need what the spec provides: before `#gen_spec`, they are generated once the
spec is finalized; after, right away. -/
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
    -- Only a property to prove needs `Init`, `NextStep`, …, which `#gen_spec` leaves to the first
    -- verification command under `veil.deferVCGeneration`. That command, here this one, generates
    -- every pending shallow definition, including those of properties declared before `#gen_spec`.
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
