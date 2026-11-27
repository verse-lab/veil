module

public meta import Veil.Frontend.DSL.Module.Elaborators.Core
public meta import Veil.Frontend.DSL.Module.Elaborators.TemporalDefinitions
public meta import Veil.Frontend.DSL.Tactic
public meta import Veil.Core.UI.Verifier.AssertionErrors
public meta import Veil.Frontend.DSL.Module.VCGen
public meta import Veil.Backend.Tactic.Frame
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
        elabVeilCommand (← liftTermElabM mod.defineFrameTheorem)
      catch ex =>
        logWarningAt invariantCmd m!"unable to define {frameTheoremName}: {ex.toMessageData}"
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

private def getVeilModuleScope : CommandElabM Elab.Command.Scope := do
  let some (_, depth) := (← localEnv.get).moduleScope? | throwUnsupportedSyntax
  let scopes ← getScopes
  return scopes[scopes.length - depth]!

/-- The declarations and VC manager survive `section` and `open … in`. Record
the derived definitions they added so the enclosing scope can recover its
module metadata without running preparation a second time. -/
private initialize preparedDefinitions : EnvExtension (NameMap (Array DerivedDefinition)) ←
  registerEnvExtension (pure {})

private def Module.prepareDeferredVerification (mod : Module) (stx : Syntax) : CommandElabM Module := do
  let ns ← getCurrNamespace
  if let some defs := (preparedDefinitions.getState (← getEnv)).find? ns then
    return ← defs.foldlM (init := mod) fun m d => m.registerDerivedDefinition d
  mod.generateDeferredWPs
  let prepared ← mod.prepareVerification stx
  let defs := prepared._derivedDefinitions.valuesArray.filter fun d => !mod._derivedDefinitions.contains d.name
  modifyEnv fun env => preparedDefinitions.modifyState env (·.insert ns defs)
  return prepared

/-- Called by the verification commands. If `#gen_spec` deferred VC generation
(`veil.deferVCGeneration`), the first call generates the deferred verification
definitions and does what `#gen_spec` skipped; otherwise this only checks that
`#gen_spec` ran. Either way, it then defines the pending shallow definitions of
temporal properties. -/
def Module.ensureVerificationSpec (mod : Module) (stx : Syntax) : CommandElabM Module := do
  mod.throwIfSpecNotFinalized
  let deferred := mod._vcGenerationDeferred
  unless deferred || mod.temporalProperties.any (·.verifyPending) do return mod
  let prepare : CommandElabM Module := do
    let mod ← if deferred then do
        let prepared ← mod.prepareDeferredVerification stx
        pure { prepared with _vcGenerationDeferred := false }
      else pure mod
    let mod ← mod.generatePendingTemporalDefinitions .verify
    localEnv.modifyModule (fun _ => mod)
    return mod
  let ns := (← getVeilModuleScope).currNamespace
  if ns == (← getCurrNamespace) then prepare
  else withScope (fun scope => { scope with currNamespace := ns }) prepare

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
    let done := mgr.isDoneFiltered (fun _ => filter)
    let results ← mgr.toResults filter (includeTheoremText := done)
    pure (results, if done then .done else .running)

private def runFilteredInvariantCheck
    (stx : Syntax)
    (mod : Module)
    (filter : VCMetadata → Bool)
    : CommandElabM Unit := do
  let managerId ← Verifier.runFilteredAsyncWithManagerId filter (logVerificationResults stx)
  -- Solver options apply where this file prepared the manager.
  let optionAnchor ← if (← getFinalizedSpec? mod.name).isSome then do
      pure <| (← localEnv.get).moduleScope?.map (·.1.raw)
    else pure mod.specFinalizedAtStx
  Verifier.displayStreamingResults stx (← captureInvariantResults managerId filter) optionAnchor

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


private structure TheoremGeneratorQueue where
  pending : Std.Queue (CommandElabM Unit) := ∅
  running : Bool := false
  deriving Inhabited

/-- Optional tools can queue checked results for publication. The Lean environment
ties the queue to the document snapshot that started the work, including across edits. -/
private initialize pendingTheoremGenerators : EnvExtension (NameMap TheoremGeneratorQueue) ←
  registerEnvExtension (pure {})

/-- Register a callback for the next publication. Throw to retry a failed import. -/
def registerTheoremGenerator (moduleName : Name) (generate : CommandElabM Unit) :
    CommandElabM Unit :=
  modifyEnv fun env => pendingTheoremGenerators.modifyState env fun queues =>
    let q := (queues.find? moduleName).getD {}
    queues.insert moduleName { q with pending := q.pending.enqueue generate }

/-- Commit one callback at a time. A nested publication leaves the FIFO to the
outer drain, including callbacks registered by the running generator. -/
private def drainTheoremGenerators (moduleName : Name) : CommandElabM Unit := do
  while true do
    liftCoreM Core.checkInterrupted
    let env ← getEnv
    let some q := (pendingTheoremGenerators.getState env).find? moduleName | return
    if q.running then return
    let some (generate, tail) := q.pending.dequeue? | return
    modifyEnv fun env => pendingTheoremGenerators.modifyState env (·.insert moduleName ⟨tail, true⟩)
    -- Restore this head on failure or interruption, including the environment
    -- from before it registered children. Earlier successful heads stay committed.
    discard <| MonadFinally.tryFinally' generate fun result =>
      if result.isNone then setEnv env else pure ()
    modifyEnv fun env => pendingTheoremGenerators.modifyState env fun queues =>
      let q := (queues.find? moduleName).getD {}
      if q.pending.isEmpty then queues.erase moduleName
      else queues.insert moduleName { q with running := false }

private def withVeilModuleScope (act : CommandElabM Unit) : CommandElabM Unit := do
  let scope ← getVeilModuleScope
  withScope (fun here => { here with currNamespace := scope.currNamespace, openDecls := scope.openDecls }) act

private def reportPublicationError (act : CommandElabM Unit) : CommandElabM Unit := do
  try act catch ex =>
    if ex.isInterrupt then throw ex
    logException ex

/-- Finish the defining file's deferred work before leaving the Veil module. -/
private def prepareModuleClose (mod : Module) : CommandElabM Unit := do
  if let some stx := mod.specFinalizedAtStx then
    if (← getFinalizedSpec? mod.name).isSome then return
    let prepared ← mod.ensureVerificationSpec stx
    Verifier.awaitAssertionChecks
    saveFinalizedSpec prepared (← ExecutionWorkflow.getDeclSources prepared)
  else
    -- A partial module can have deferred action definitions without a spec.
    mod.generateDeferredWPs

private def publishRequestedChecks (mod : Module) : CommandElabM Unit := do
  reportPublicationError (Verifier.publishRequestedTheorems mod.name)
  -- Keep a failing close open for retry. A callback declining its own syntax
  -- must not tell Lean to fall through to the builtin `end` elaborator.
  try drainTheoremGenerators mod.name catch ex =>
    if let .internal id .. := ex then
      if id == unsupportedSyntaxExceptionId then
        throwError "a theorem generator for `{mod.name}` encountered unsupported syntax"
      if isAbortExceptionId id && !(← MonadLog.hasErrors) then
        throwError "a theorem generator for `{mod.name}` aborted publication"
    throw ex

@[command_elab Veil.genTheorems]
def elabGenTheorems : CommandElab := fun _ => do
  let mod ← getCurrentModule
  mod.throwIfSpecNotFinalized
  withVeilModuleScope <| publishRequestedChecks mod

/-- A named Lean `end` can close several scopes at once. Only publish if it closes
the Veil module. Leave other closes and malformed names to Lean's elaborator. -/
@[scoped command_elab Lean.Parser.Command.«end»]
def elabVeilEnd : CommandElab := fun stx => do
  let some (_, depth) := (← localEnv.get).moduleScope? | throwUnsupportedSyntax
  let `(end $[$header? $[.%$_$_]?]?) := stx | throwUnsupportedSyntax
  let scopes ← getScopes
  let count := header?.map (·.getId.getNumParts) |>.getD 1
  unless scopes.length - depth < count && count < scopes.length do throwUnsupportedSyntax
  match header? with
  | none => unless scopes.head!.header.isEmpty do throwUnsupportedSyntax
  | some header =>
    let candidates := scopes.take count
    unless candidates.all (fun s => !s.header.isEmpty) &&
        header.getId.components.reverse == candidates.map (Name.mkSimple ·.header) do
      throwUnsupportedSyntax
  let mod ← getCurrentModule
  withVeilModuleScope do
    reportPublicationError (prepareModuleClose mod)
    publishRequestedChecks mod
  elabEnd stx

@[scoped command_elab Lean.Parser.Command.eoi, scoped command_elab Lean.Parser.Command.exit]
def elabUnclosedVeilModule : CommandElab := fun _ => do
  let some (opener, _) := (← localEnv.get).moduleScope? | throwUnsupportedSyntax
  throwErrorAt opener "Unclosed Veil module `{opener.getId}`. Close it with `end {opener.getId}`."

end Veil
