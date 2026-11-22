module

public meta import Veil.Frontend.DSL.Module.Elaborators.Core
public meta import Veil.Frontend.DSL.Module.Elaborators.TemporalDefinitions
public meta import Veil.Frontend.DSL.Tactic
public meta import Veil.Core.UI.Verifier.AssertionErrors
public meta import Veil.Frontend.DSL.Module.VCGen
public meta import Veil.Core.Tools.Verifier.Server
public meta import Veil.Core.Tools.Verifier.Results
meta import Veil.Core.Tools.Verifier.TheoremDischarger
public meta import Veil.Core.UI.Verifier.VerificationResults
public meta import Veil.Util.StreamingInfo

public meta section

open Lean Parser Elab Command Term
open scoped Veil.Extract
namespace Veil

private def warnIfNoInvariantsDefined (mod : Module) : CommandElabM Unit := do
  if mod.invariants.isEmpty && mod.temporalProperties.isEmpty then
    logWarning "you have not defined any invariants or temporal properties for this specification; did you forget?"

private def warnIfNoActionsDefined (mod : Module) : CommandElabM Unit := do
  if mod.actions.isEmpty then
    logWarning "you have not defined any actions for this specification; did you forget?"

private def throwIfNoInitializerDefined (mod : Module) : CommandElabM Unit := do
  unless mod.procedures.any (·.info matches .initializer) do
    throwError "no `after_init` block has been defined for this specification; every Veil module must have one"

/-- Assemble the symbolic transition system and generate the verification
conditions, starting the `doesNotThrow` checks. This needs the WP-based
verification definitions of every procedure. -/
private def Module.prepareVerification (mod : Module) (stx : Syntax) : CommandElabM Module := do
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
    let (nextTrCmds, mod) ← mod.assembleNextTrAndStep
    for cmd in nextTrCmds do elabVeilCommand cmd
    try
      liftTermElabM mod.defineTransitionAbstractForNext
    catch ex =>
      logWarningAt stx m!"unable to prove {toTransitionAbstractName assembledNextName}: {ex.toMessageData}"
    let (initCmd, mod) ← mod.assembleInit
    elabVeilCommand initCmd
    let (rtsCmd, mod) ← Module.assembleRelationalTransitionSystem mod
    elabVeilCommand rtsCmd
    pure mod
  Verifier.runManager
  mod.generateDoesNotThrowVCs
  -- Warn at the assertion site. Explicit invariant checks report failed VCs at the command.
  Verifier.runFilteredAsync Verifier.isDoesNotThrow logDoesNotThrowWarnings (publish := false)
  mod.generateInvariantVCs
  -- Invariant VCs are generated here; verifier commands decide when to start them.
  return mod

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
      -- Temporal proofs also need the simplified core of the empty conjunction (`True`).
      try
        liftTermElabM $ mod.simplifyLocalRPropCore assembledInvariantsName
      catch ex =>
        logWarningAt invariantCmd m!"unable to synthesize LocalRProp instance for {assembledInvariantsName}: {ex.toMessageData}"
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
  let mod ← mod.generatePendingTemporalDefinitions .check
  -- With `veil.deferVCGeneration`, the verification conditions and everything
  -- else that needs the actions' WPs, including the `doesNotThrow` checks, wait
  -- for a verification command.
  let mod ← if veil.deferVCGeneration.get (← getOptions) then do
      -- Capture an independent owner while verification generation is deferred.
      Verifier.runManager
      pure { mod with _vcGenerationDeferred := true }
    else do
      -- The option may have been set for some declarations and turned off
      -- since; generate what they deferred, then finalize as usual.
      mod.generateDeferredWPs
      mod.prepareVerification stx
  return { mod with _specFinalizedAt := some stx }

/-- Preparing a finalized spec adds declarations that survive `set_option … in`
and section boundaries. Remember the corresponding module metadata in the same
Lean checkpoint so closing the scope cannot request preparation a second time. -/
private initialize preparedVerificationExt : EnvExtension (NameMap Module) ←
  registerEnvExtension (pure {})

/-- Called by the verification commands. If `#gen_spec` deferred VC generation
(`veil.deferVCGeneration`), the first call generates the deferred verification
definitions and does what `#gen_spec` skipped; otherwise this only checks that
`#gen_spec` ran. Either way, it then defines the pending shallow definitions of
temporal properties. -/
def Module.ensureVerificationSpec (mod : Module) (stx : Syntax) : CommandElabM Module := do
  mod.throwIfSpecNotFinalized
  let deferred := mod._vcGenerationDeferred
  unless deferred || mod.temporalProperties.any (·.verifyPending) do return mod
  if let some prepared := (preparedVerificationExt.getState (← getEnv)).find? mod.name then
    localEnv.modifyModule (fun _ => prepared)
    return prepared
  let mut mod := mod
  if deferred then
    mod.generateDeferredWPs
    mod ← mod.prepareVerification stx
    mod := { mod with _vcGenerationDeferred := false }
  mod ← mod.generatePendingTemporalDefinitions .verify
  modifyEnv fun env => preparedVerificationExt.modifyState env (·.insert mod.name mod)
  localEnv.modifyModule (fun _ => mod)
  return mod

/-- The tactics of the proof `tacs`, to splice after generated tactics in a single
sequence rather than nest `tacs` as `($tacs)`, a single tactic: once a tactic of a
sequence changes, Lean cancels what still runs of its previous version, so any edit
to the proof would restart its running tactics instead of waiting for them. -/
def tacticSeqSteps (tacs : TSyntax ``Parser.Tactic.tacticSeq) : Syntax.TSepArray `tactic ";" :=
  match tacs with
  | `(tacticSeq| $steps;*) => steps
  | _ => ⟨#[tacs.raw[0]]⟩  -- `{ … }` is a tactic itself

-- NOTE: Taking some inspiration from how incrementality was done in Velvet
/-- Generate a theorem whose proof starts with `unveil`. `@[incremental]` keeps
the command's snapshot bundle available for Lean's theorem/tactic elaborators;
stable generated syntax lets them reuse the unchanged proof prefix. -/
@[command_elab Veil.proveVeilInvariantGoal, incremental]
def elabProveVeilInvariantGoal : CommandElab := fun stx => do
  let (actionId, propertyId, style, byTk, proof) ← match stx with
    | `(command| prove_veil_invariant_goal $actionId $propertyId using wp by%$byTk $proof:tacticSeq) =>
      pure (actionId, propertyId, VCStyle.wp, byTk, proof)
    | `(command| prove_veil_invariant_goal $actionId $propertyId using tr by%$byTk $proof:tacticSeq) =>
      pure (actionId, propertyId, VCStyle.tr, byTk, proof)
    | _ => throwUnsupportedSyntax
  let mod ← getCurrentModule (errMsg := "You cannot prove a Veil invariant goal outside of a Veil module!")
  mod.throwIfSpecNotFinalized
  -- Key quotation hygiene by the goal identity. The default seed includes the
  -- whole command's text, so editing a tactic would change generated names.
  withInitQuotContext (some (hash (← getCurrNamespace, actionId.getId, propertyId.getId, style))) do
    -- Anchor generated syntax to the selector: the whole command's end position
    -- moves on proof edits. The antiquoted user proof retains its own positions.
    withRef actionId do
      -- Deferred preparation elaborates multiple helper declarations. Hide the
      -- outer snapshot bundle from them, then restore it for the theorem below.
      -- Do not use `withoutCommandIncrementality true`: it also cancels the old
      -- snapshot tree, including in-flight tactics the theorem may still reuse.
      let mod ← withReader (fun ctx => { ctx with snap? := none }) <|
        mod.ensureVerificationSpec actionId
      let vc ← mod.mkInvariantGoalVC actionId propertyId style
      let thmId := mkIdentFrom actionId vc.name
      -- The visible `by` token should show the simplified goal, including when
      -- the user has not written any tactics yet.
      let entry : TSyntax `tactic := ⟨(← `(tactic| skip)).raw.setInfo byTk.getHeadInfo⟩
      let steps := tacticSeqSteps proof
      let cmd ← `(command|
        @[veil] theorem $thmId $(vc.params)* : $(vc.statement) := by
          unveil
          $entry:tactic
          $steps;*)
      -- Delegate directly to Lean's theorem/tactic elaborators so their snapshot
      -- tree can reuse `unveil` and the unchanged prefix of the user's proof.
      -- They compare the generated syntax and cancel the parts invalidated by
      -- edits to the selected goal or proof; we must not cancel them beforehand.
      elabCommand cmd

@[command_elab Veil.genSpec]
def elabGenSpec : CommandElab := fun stx => do
  -- Use dynamic trace class name for detailed profiling
  withTraceNode `veil.perf.elaborator.genSpec (fun _ => return "#gen_spec") do
    let mod ← getCurrentModule (errMsg := "You cannot elaborate a specification outside of a Veil module!")
    let mod ← mod.ensureSpecIsFinalized stx
    -- A previous #gen_spec may have finalized the spec while deferring verification.
    let mod ← if veil.deferVCGeneration.get (← getOptions) then pure mod
      else mod.ensureVerificationSpec stx
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
  let fileMap ← getFileMap
  -- Keep enclosing commands such as `set_option ... in` on the check.
  let insertPos := fileMap.lineStart (fileMap.toPosition (← read).cmdPos).line
  -- Insert before the line rather than replacing the command, preserving its
  -- indentation and exact source text (including multiline syntax).
  let insertSpan := Syntax.ofRange { start := insertPos, stop := insertPos }
  let label := "Insert theorem stubs for undischarged verification conditions"
  let suggestion : Lean.Meta.Tactic.TryThis.Suggestion := {
    suggestion := .string (theoremText ++ "\n\n")
    toCodeActionTitle? := some fun _ => label
  }
  liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion stx suggestion
    (origSpan? := some insertSpan) (header := s!"{label}:\n")

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

/-- Bind the widget to the generation requested by its asynchronous observer. -/
private def captureInvariantResults (managerId : ManagerId) (filter : VCMetadata → Bool)
    : CommandElabM (CoreM (VerificationResults VCMetadata SmtResult × Verifier.StreamingStatus)) := do
  let owner ← Verifier.getVCManagerOwner
  let getManager ← Verifier.captureVCManager
  return do
    -- CAREFUL: do not hold the lock to print
    let mgr ← getManager
    if (← owner.cancelTk.isSet) || mgr._managerId != managerId then
      throwError "verification interrupted: specification owner was canceled or reset"
    let done := mgr.isDoneFiltered filter
    let results ← mgr.toResults filter (includeTheoremText := done)
    pure (results, if done then .done else .running)

private def runFilteredInvariantCheck
    (stx : Syntax)
    (mod : Module)
    (filter : VCMetadata → Bool)
    : CommandElabM Unit := do
  let managerId ← Verifier.runFilteredAsyncWithManagerId filter (logVerificationResults stx)
  Verifier.displayStreamingResults stx (← captureInvariantResults managerId filter)
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

@[command_elab Veil.checkInvariants, incremental]
def elabCheckInvariants : CommandElab := fun stx => withStreamingInfo stx do
  -- Use dynamic trace class name for detailed profiling
  withTraceNode `veil.perf.elaborator.checkInvariants (fun _ => return "#check_invariants") do
    -- Skip in compilation mode (no verification feedback needed)
    let mod ← getCurrentModule (errMsg := "You cannot #check_invariant outside of a Veil module!")
    let mod ← mod.ensureVerificationSpec stx
    runFilteredInvariantCheck stx mod VCMetadata.isInduction

@[command_elab Veil.checkAction, incremental]
def elabCheckAction : CommandElab := fun stx => do
  unless stx.getKind == `Veil.checkAction do
    throwUnsupportedSyntax
  withStreamingInfo stx do
  withTraceNode `veil.perf.elaborator.checkAction (fun _ => return "#check_action") do
    let mod ← getCurrentModule (errMsg := "You cannot #check_action outside of a Veil module!")
    mod.throwIfSpecNotFinalized
    let actionName := stx[1].getId
    unless (getCheckableAction? mod actionName).isSome do
      throwUnknownCheckAction mod actionName
    let mod ← mod.ensureVerificationSpec stx
    runFilteredInvariantCheck stx mod (isInductionForAction actionName)


/-- Optional tools can queue checked results for `#gen_theorems`. Keeping these actions in the
environment ties them to the document snapshot that started the work, including across edits. -/
private initialize pendingTheoremGenerators : EnvExtension (NameMap (Array (CommandElabM Unit))) ←
  registerEnvExtension (pure {})

def registerTheoremGenerator (moduleName : Name) (generate : CommandElabM Unit) :
    CommandElabM Unit :=
  modifyEnv fun env => pendingTheoremGenerators.modifyState env fun pending =>
    pending.insert moduleName ((pending.find? moduleName).getD #[] |>.push generate)

/-- Publish in the scope where the module was opened, even inside a helper namespace. -/
private def finishRequestedChecks (closing := false) : CommandElabM Unit := do
  let mod ← getCurrentModule
  let some (_, depth) := (← localEnv.get).moduleScope? | throwUnsupportedSyntax
  let scopes ← getScopes
  let moduleScope := scopes[scopes.length - depth]!
  withScope (fun here => { here with currNamespace := moduleScope.currNamespace, openDecls := moduleScope.openDecls }) do
    let report (act : CommandElabM Unit) := do
      try act catch ex =>
        if ex.isInterrupt then throw ex
        logException ex
    if closing then
      if let some stx := mod.specFinalizedAtStx then
        report do
          discard <| mod.ensureVerificationSpec stx
          Verifier.awaitAssertionChecks
      else
        -- A partial module can have deferred action definitions without a spec.
        report mod.generateDeferredWPs
    report (Verifier.publishRequestedTheorems mod.name)
    let generators := (pendingTheoremGenerators.getState (← getEnv)).find? mod.name |>.getD #[]
    modifyEnv fun env => pendingTheoremGenerators.modifyState env (·.erase mod.name)
    for generate in generators do report generate

@[command_elab Veil.genTheorems]
def elabGenTheorems : CommandElab := fun _ => finishRequestedChecks (closing := false)

/-- A named Lean `end` can close several scopes at once. Only publish if it closes
the Veil module. Leave other closes and malformed names to Lean's elaborator. -/
@[scoped command_elab Lean.Parser.Command.«end»]
def elabVeilEnd : CommandElab := fun stx => do
  let some (_, depth) := (← localEnv.get).moduleScope? | throwUnsupportedSyntax
  let `(end $header:ident $[.%$_$_]?) := stx | throwUnsupportedSyntax
  let scopes ← getScopes
  let names := header.getId.components
  unless scopes.length - depth < names.length && names.length < scopes.length &&
      names.reverse == (scopes.take names.length).map (Name.mkSimple ·.header) do
    throwUnsupportedSyntax
  finishRequestedChecks (closing := true)
  elabEnd stx

@[scoped command_elab Lean.Parser.Command.eoi, scoped command_elab Lean.Parser.Command.exit]
def elabUnclosedVeilModule : CommandElab := fun _ => do
  let some (opener, _) := (← localEnv.get).moduleScope? | throwUnsupportedSyntax
  throwErrorAt opener "Unclosed Veil module `{opener.getId}`. Close it with `end {opener.getId}`."

end Veil
