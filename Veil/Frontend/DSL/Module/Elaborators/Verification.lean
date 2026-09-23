module

public meta import Veil.Frontend.DSL.Module.Elaborators.Core
public meta import Veil.Frontend.DSL.Tactic
public meta import Veil.Core.UI.Verifier.AssertionErrors
public meta import Veil.Frontend.DSL.Module.VCGen
public meta import Veil.Core.Tools.Verifier.Server
public meta import Veil.Core.Tools.Verifier.Results
public meta import Veil.Core.UI.Verifier.VerificationResults

public meta section

open Lean Parser Elab Command Term
open scoped Veil.Extract
namespace Veil

private def warnIfNoInvariantsDefined (mod : Module) : CommandElabM Unit := do
  if mod.invariants.isEmpty then
    logWarning "you have not defined any invariants for this specification; did you forget?"

private def warnIfNoActionsDefined (mod : Module) : CommandElabM Unit := do
  if mod.actions.isEmpty then
    logWarning "you have not defined any actions for this specification; did you forget?"

private def throwIfNoInitializerDefined (mod : Module) : CommandElabM Unit := do
  unless mod.procedures.any (·.info matches .initializer) do
    throwError "no `after_init` block has been defined for this specification; every Veil module must have one"

/-- Crystallizes the specification of the module, i.e. it finalizes the set of
`procedures` and `assertions`. The `stx` parameter is the syntax of the command
that triggered the finalization; it is stored for use by `#model_check` when
generating compiled model source. -/
def Module.ensureSpecIsFinalized (mod : Module) (stx : Syntax) : CommandElabM Module := do
  if mod.isSpecFinalized then return mod
  let mod ← mod.ensureStateIsDefined
  throwIfNoInitializerDefined mod
  warnIfNoInvariantsDefined mod
  warnIfNoActionsDefined mod
  let mod ← do
    let mod ← withTraceNode `veil.perf.elaborator.decl.Assumptions (fun _ => return "Assumptions") do
      let (assumptionCmd, mod) ← mod.assembleAssumptions
      elabVeilCommand assumptionCmd
      if !mod.assumptions.isEmpty then
        liftTermElabM do
          mod.tryDefineLocalAbstractEqForTheoryPredicate assembledAssumptionsName assumptionCmd
      try
        liftTermElabM $ mod.simplifyLocalTheoryPropCore assembledAssumptionsName
      catch ex =>
        logWarningAt assumptionCmd m!"unable to synthesize LocalTheoryProp simplified core for {assembledAssumptionsName}: {ex.toMessageData}"
      return mod
    let mod ← withTraceNode `veil.perf.elaborator.decl.Invariants (fun _ => return "Invariants") do
      let (invariantCmd, mod) ← mod.assembleInvariants
      trace[veil.debug] s!"Elaborating invariants: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic invariantCmd}"
      elabVeilCommand invariantCmd
      if !mod.invariants.isEmpty then
        try
          liftTermElabM $ mod.simplifyLocalRPropCore assembledInvariantsName
        catch ex =>
          logWarningAt invariantCmd m!"unable to synthesize LocalRProp instance for {assembledInvariantsName}: {ex.toMessageData}"
      if !mod.invariants.isEmpty then
        try
          let localMeetsCmd ← liftTermElabM mod.defineMeetsSpecificationIfSuccessfulAssumingLocalTheorem
          elabVeilCommand localMeetsCmd
        catch ex =>
          logWarningAt invariantCmd m!"unable to define {localMeetsSpecificationIfSuccessfulAssumingName}: {ex.toMessageData}"
        try
          let localTrMeetsCmd ← liftTermElabM mod.defineTransitionMeetsSpecificationIfSuccessfulAssumingLocalTheorem
          elabVeilCommand localTrMeetsCmd
        catch ex =>
          logWarningAt invariantCmd m!"unable to define {localTransitionMeetsSpecificationIfSuccessfulAssumingName}: {ex.toMessageData}"
      return mod
    let mod ← withTraceNode `veil.perf.elaborator.decl.Safeties (fun _ => return "Safeties") do
      let (safetyCmd, mod) ← mod.assembleSafeties
      trace[veil.debug] s!"Elaborating safeties: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic safetyCmd}"
      elabVeilCommand safetyCmd
      return mod
    pure mod
  let (labelCmds, mod) ← mod.assembleLabel
  for cmd in labelCmds do
    elabVeilCommand cmd

  -- Generate ActionTag type for symbolic model checking
  -- NOTE: ActionTag is query-local (not a module sort), but we generate the
  -- axiomatisation class and concrete type here for convenience
  let actionNames := mod.actions.map (fun (a : ProcedureSpecification) => Lean.mkIdent a.name)
  if !actionNames.isEmpty then
    let (className, classDecl) ← mkEnumAxiomatisation actionTagType actionNames
    elabVeilCommand classDecl
    for cmd in (← mkEnumConcreteType actionTagType actionNames) do
      elabVeilCommand cmd
    elabVeilCommand $ ← `(open $className:ident)
    -- TODO: Generate equivalence theorem (ActionTag.label_equiv) here

  let mod ← do
    let (nextCmd, mod) ← mod.assembleNext
    elabVeilCommand nextCmd
    let (nextTrCmd, mod) ← mod.assembleNextTransition
    elabVeilCommand nextTrCmd
    let nextTr'Cmd ← mod.assembleNextTransition'
    elabVeilCommand nextTr'Cmd
    try
      if let some abstractNextCmd ← liftTermElabM mod.defineTransitionAbstractForNext then
        elabVeilCommand abstractNextCmd
    catch ex =>
      logWarningAt stx m!"unable to prove {toTransitionAbstractName assembledNextName}: {ex.toMessageData}"
    let (initCmd, mod) ← mod.assembleInit
    elabVeilCommand initCmd
    let (rtsCmd, mod) ← Module.assembleRelationalTransitionSystem mod
    elabVeilCommand rtsCmd
    pure mod
  Verifier.runManager
  mod.generateDoesNotThrowVCs
  -- Run doesNotThrow VCs asynchronously and log errors at assertion locations when done
  Verifier.runFilteredAsync Verifier.isDoesNotThrow logDoesNotThrowErrors
  mod.generateInvariantVCs
  -- Invariant VCs are generated here; verifier commands decide when to start them.
  return { mod with _specFinalizedAt := some stx }

@[command_elab Veil.genSpec]
def elabGenSpec : CommandElab := fun stx => do
  -- Use dynamic trace class name for detailed profiling
  withTraceNode `veil.perf.elaborator.genSpec (fun _ => return "#gen_spec") do
    let mod ← getCurrentModule (errMsg := "You cannot elaborate a specification outside of a Veil module!")
    let mod ← mod.ensureSpecIsFinalized stx
    localEnv.modifyModule (fun _ => mod)

private def proofHasSorryGoalCount (results : VerificationResults VCMetadata SmtResult) : Nat :=
  results.vcs.foldl (init := 0) fun count vc =>
    if vc.proofHasSorry then count + 1 else count

private def trustedSmtWarning (count : Nat) : MessageData :=
  let goalWord := if count == 1 then "goal" else "goals"
  m!"Trusting SMT solver for {count} {goalWord}. `set_option veil.smt.trust false` to enable proof reconstruction."

private def addUndischargedTheoremSuggestion
    (stx : Syntax) (results : VerificationResults VCMetadata SmtResult) : CommandElabM Unit := do
  let some theoremText := Verifier.undischargedTheoremStubsText results | return
  let replacement ← match stx.getPos?, stx.getTailPos? with
    | some startPos, some endPos =>
      let commandText := String.Pos.Raw.extract (← getFileMap).source startPos endPos
      pure s!"{commandText}\n\n{theoremText}"
    | _, _ =>
      pure theoremText
  let label := "Insert theorem stubs for undischarged verification conditions"
  let suggestion : Lean.Meta.Tactic.TryThis.Suggestion := {
    suggestion := .string replacement
    toCodeActionTitle? := some fun _ => label
  }
  liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion stx suggestion
    (header := s!"{label}:\n")

/-- Log verification results asynchronously after all VCs complete. -/
def logVerificationResults (stx : Syntax) (results : VerificationResults VCMetadata SmtResult) : CommandElabM Unit := do
  let msg ← Verifier.formatVerificationResults results
  let violationIsError := veil.violationIsError.get (← getOptions)
  if Verifier.hasFailedVCs results && violationIsError then
    logErrorAt stx msg
  else
    logInfoAt stx msg
  let trustedCount := proofHasSorryGoalCount results
  if trustedCount > 0 then
    logWarningAt stx (trustedSmtWarning trustedCount)
  addUndischargedTheoremSuggestion stx results

private def runFilteredInvariantCheck
    (stx : Syntax)
    (mod : Module)
    (filter : VCMetadata → Bool)
    : CommandElabM Unit := do
  Verifier.runFilteredAsync filter (logVerificationResults stx)
  Verifier.displayStreamingResults stx
    (do
      -- CAREFUL: do not hold the lock to print
      let mgr ← Verifier.vcManager.atomically fun ref => ref.get
      let done := mgr.isDoneFiltered filter
      let results ← mgr.toResults filter (includeTheoremText := done)
      pure (results, if done then .done else .running))
    mod.specFinalizedAtStx

private def isInductionForAction (actionName : Name) : VCMetadata → Bool
  | .induction m => m.action == actionName
  | .trace _ => false

private def getCheckableAction? (mod : Module) (actionName : Name) : Option ProcedureSpecification :=
  mod.procedures.find? fun proc =>
    proc.name == actionName &&
    match proc.info with
    | .action _ _ => true
    | .initializer | .procedure _ => false

private def throwUnknownCheckAction (mod : Module) (actionName : Name) : CommandElabM α := do
  let availableActions := mod.procedures.filterMap fun proc =>
    match proc.info with
    | .action _ _ => some proc.name.toString
    | .initializer | .procedure _ => none
  let suggestion :=
    if availableActions.isEmpty then
      "This module does not define any actions."
    else
      s!"Available actions: {", ".intercalate availableActions.toList}"
  throwError s!"Unknown action {actionName} for #check_action. {suggestion}"

@[command_elab Veil.checkInvariants]
def elabCheckInvariants : CommandElab := fun stx => do
  -- Use dynamic trace class name for detailed profiling
  withTraceNode `veil.perf.elaborator.checkInvariants (fun _ => return "#check_invariants") do
    -- Skip in compilation mode (no verification feedback needed)
    let mod ← getCurrentModule (errMsg := "You cannot #check_invariant outside of a Veil module!")
    mod.throwIfSpecNotFinalized
    runFilteredInvariantCheck stx mod VCMetadata.isInduction

@[command_elab Veil.checkAction]
def elabCheckAction : CommandElab := fun stx => do
  withTraceNode `veil.perf.elaborator.checkAction (fun _ => return "#check_action") do
    let mod ← getCurrentModule (errMsg := "You cannot #check_action outside of a Veil module!")
    mod.throwIfSpecNotFinalized
    unless stx.getKind == `Veil.checkAction do
      throwUnsupportedSyntax
    let actionName := stx[1].getId
    unless (getCheckableAction? mod actionName).isSome do
      throwUnknownCheckAction mod actionName
    runFilteredInvariantCheck stx mod (isInductionForAction actionName)


@[command_elab Veil.genTheorems]
def elabGenTheorems : CommandElab := fun _stx => do
  withTraceNode `veil.perf.elaborator.genTheorems (fun _ => return "#gen_theorems") do
    let mod ← getCurrentModule (errMsg := "You cannot #gen_theorems outside of a Veil module!")
    mod.throwIfSpecNotFinalized
    let _ ← Verifier.waitFilteredSync (fun _ => true)
    Verifier.addProvenTheoremsInDependencyOrder (fun _ => true)

end Veil
