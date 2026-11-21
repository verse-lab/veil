module

public meta import Lean
meta import Batteries.Linter.UnreachableTactic
public meta import Veil.Util.Meta
public meta import Veil.Backend.SMT.Result
public meta import Veil.Frontend.DSL.Module.Representation
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Core.Tools.Verifier.Server
public meta import Veil.Core.UI.Verifier.Model

public meta section

/-!
# VC Generation Common Utilities

This module provides shared infrastructure for VC generation and discharging,
used by both inductive VCs and trace VCs.
-/

open Lean Elab Term Command

namespace Veil

/-! ## SMT Channel Utilities -/

/-- Collect SMT outputs from the async channel.
    Closes the channel and collects all available outputs. -/
def collectSmtOutputs [Monad m] [MonadError m] [MonadLiftT BaseIO m]
    [MonadLiftT (EIO Std.CloseableChannel.Error) m]
    (ch : Std.CloseableChannel ((Name × Nat) × Smt.AsyncOutput)) (expectedName : Name)
    : m (Array SmtOutput) := do
  -- Calling `close` will throw an exception if the channel is already closed.
  -- We ignore it here because we want to continue with our logic.
  try let _ ← ch.close catch _ => pure ()
  let mut outputs := #[]
  while true do
    let Option.some ((name, index), output) := (← ch.recv).get | break
    if name != expectedName then
      let s := s!"Expected {expectedName}, got {name} from channel"
      dbg_trace s; throwError s
    outputs := outputs.push ((name, index), output)
  return outputs

/-- Extract an unknown reason from an exception when it represents a solver
outcome that should be surfaced as `unknown` rather than `error`. -/
def unknownReasonFromException? [Monad m] [MonadLiftT BaseIO m]
    (ex : Exception) : m (Option String) := do
  let message ← ex.toMessageData.toString
  if unknownExplanation? message == some .incomplete then
    return some message
  return none

/-- Categorize SMT outputs into separate arrays for errors, sat, unknown, and unsat results. -/
def categorizeSmtOutputs [Monad m] [MonadLiftT BaseIO m] (outputs : Array SmtOutput)
    : m (Array Exception × Array (Option Smt.Model) × Array String × Array SmtUnsatCore) := do
  let mut (errors, sat, unknown, unsat) := (#[], #[], #[], #[])
  for output in outputs do
    match output with
    | (_, .exception ex) =>
      match ← unknownReasonFromException? ex with
      | some reason => unknown := unknown.push reason
      | none => errors := errors.push ex
    | (_, .result (.sat ce)) => sat := sat.push ce
    | (_, .result (.unknown reason)) => unknown := unknown.push reason
    | (_, .result (.unsat _ core)) => unsat := unsat.push core
    | _ => pure ()
  return (errors, sat, unknown, unsat)

/-- Build SmtResult from categorized outputs using a custom SAT handler.
    The satHandler processes SAT model results (e.g., builds counterexamples).
    Priority: errors > sat > unknown > unsat -/
def buildSmtResult [Monad m] [MonadError m] [MonadLiftT BaseIO m]
    (outputs : Array SmtOutput)
    (satHandler : Array (Option Smt.Model) → m (Array (Option AnnotatedSmtModel)))
    : m (Option SmtResult) := do
  let (errors, sat, unknown, unsat) ← categorizeSmtOutputs outputs

  if errors.size > 0 then
    return .some $ .error (← errors.mapM (fun ex => do
      return (ex, toJson (← ex.toMessageData.toString))))

  if sat.size > 0 then
    return .some $ .sat (← satHandler sat)

  if unknown.size > 0 then
    return .some $ .unknown unknown

  if errors.size == 0 && sat.size == 0 && unknown.size == 0 && unsat.size > 0 then
    return .some $ .unsat unsat

  -- the SMT solver wasn't involved in proving this goal
  return .none

/-- Create a discharger that elaborates `term` against the VC statement's type
    and builds its result via `mkResult`.

    `mkResult` runs inside `liftTermElabM` and receives the SMT output channel,
    either the elaborated witness (`.inl`) or the exception that interrupted
    elaboration (`.inr`), and the elapsed time in milliseconds. -/
def Discharger.fromTermWith (term : Term) (vcStatement : VCStatement)
    (dischargerId : DischargerIdentifier)
    (ch : Std.Channel (ManagerNotification VCMetadata SmtResult))
    (mkResult : Std.CloseableChannel ((Name × Nat) × Smt.AsyncOutput) →
      Witness ⊕ Exception → Nat → TermElabM (DischargerResult SmtResult))
    (traceLabel : String := "discharger") (quietOnUnknown : Bool := false)
    (proof? : Option (TermElabM Witness) := none) :
    CommandElabM (Discharger SmtResult) := do
  let cancelTk ← IO.CancelToken.new
  let smtCh ← Std.CloseableChannel.new
  -- Create promises to track start time and result
  let startTimePromise ← IO.Promise.new
  let resultPromise ← IO.Promise.new
  -- Use wrapAsyncAsSnapshot for proper snapshot tree integration with the language server
  let savedState ← get
  let mk ← try
    -- Automatic workers need the specification environment, but never own its
    -- mutable runtime. Exclude handles from the worker's current environment.
    -- Declaration realization contexts may still retain older environments;
    -- the origin snapshot's lifetime cleanup releases abandoned task closures.
    -- wrapAsync captures state before its execution-time resets. Strip earlier
    -- diagnostics, info trees and snapshots as well: they can hold environments
    -- or observer closures pointing back to this runtime.
    modify fun st => { st with
      env := Veil.Verifier.clearVerifierRuntime st.env
      messages := {}
      infoState := { enabled := st.infoState.enabled }
      traceState := {}
      snapshotTasks := #[] }
    -- `wrapAsync` installs the worker's token, but `wrapAsyncAsSnapshot` also
    -- retains the outer context for diagnostics. Strip the parent's snapshot
    -- and token so queued workers cannot retain a caller's cancellation handle.
    withReader (fun ctx : Command.Context => { ctx with snap? := none, cancelTk? := none }) do
      Command.wrapAsyncAsSnapshot (fun vcStatement : VCStatement => do
        -- Resolve the start time promise when the discharger actually begins
        let startTime ← IO.monoMsNow
        startTimePromise.resolve startTime
        let res ← (do
          try
            -- Wrap in profiler trace for discharger timing
            withTraceNode (`veil.perf.discharger ++ dischargerId.name)
                (fun _ => return s!"{traceLabel} {dischargerId.name}") do
              liftTermElabM $ do
                let witness ← match proof? with
                  | some build => build
                  | none => do
                    let _ ← Smt.initAsyncState dischargerId.name (.some smtCh)
                    instantiateMVars $ ← withSynthesize (postpone := .no) $
                      withoutErrToSorry $ elabTermEnsuringType term (← vcStatement.type)
                let endTime ← IO.monoMsNow
                mkResult smtCh (.inl witness) (endTime - startTime)
          catch ex =>
            --`mkResult` can throw, but a result must be published on every path.
            let endTime ← IO.monoMsNow
            try
              liftTermElabM $ mkResult smtCh (.inr ex) (endTime - startTime)
            catch ex2 =>
              return .error #[← safeExceptionEntry ex, ← safeExceptionEntry ex2]
                (endTime - startTime)
        )
        -- Proof-search failures are discharger results. Do not also publish them
        -- as command errors when a later discharger may still prove the VC.
        if quietOnUnknown && (res matches .unknown ..) then
          modify fun st => { st with messages := {}, snapshotTasks := #[] }
        publishDischargerResult resultPromise ch dischargerId res
      ) cancelTk
  finally
    -- Keep wrapAsync's fresh name-generator advances while restoring all
    -- caller diagnostics/UI state and its original manager-bearing environment.
    modify fun st => { st with
      env := savedState.env
      messages := savedState.messages
      infoState := savedState.infoState
      traceState := savedState.traceState
      snapshotTasks := savedState.snapshotTasks }
  let run : BaseIO Language.SnapshotTree := do
    let startTime ← IO.monoMsNow
    let snapshot ← mk vcStatement
    -- The snapshot wrapper turns interrupts into an empty snapshot, possibly
    -- skipping publication. Finish here in BaseIO, after the cancellable body
    -- has exited on this same worker. Preserve any result it already published.
    unless ← resultPromise.isResolved do
      let ex := Exception.error term
        m!"Discharger {dischargerId.name} interrupted before producing a result"
      let endTime ← IO.monoMsNow
      publishDischargerResult resultPromise ch dischargerId
        (.error #[← safeExceptionEntry ex] (endTime - startTime))
    return snapshot
  -- Dedicated thread: the task blocks in in-process solver FFI for its whole
  -- duration, which would starve the bounded elaboration thread pool
  let mkTask := run.asTask (prio := .dedicated)
  return {
    id := dischargerId,
    term := term,
    cancelTk := cancelTk,
    task := Option.none,
    startTimePromise := startTimePromise,
    resultPromise := resultPromise,
    mkTask := mkTask
  }

private inductive AutomaticDischarger where
  | frame
  | smt
  | custom (name : Name) (appliesTo : VCMetadata → Bool) (term : Term)
  deriving Inhabited

private def AutomaticDischarger.name : AutomaticDischarger → Name
  | .frame => `frame
  | .smt => `smt
  | .custom name .. => name

private initialize automaticDischargers :
    SimpleScopedEnvExtension (Array AutomaticDischarger) (Array AutomaticDischarger) ←
  registerSimpleScopedEnvExtension {
    initial := #[.frame, .smt]
    addEntry := fun _ entries => entries
  }

/-- Append a proof tactic for subsequently generated VCs in this Lean scope.
    Omit `for induction` or `for trace` to target both kinds. -/
scoped syntax (name := veilDischarger) "veil_discharger " rawIdent (" for " rawIdent)? " := " term : command

-- The tactic is intentionally elaborated later, once per applicable VC.
initialize
  Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``veilDischarger
  Lean.Linter.Extra.UnreachableTactic.addIgnoreTacticKind ``veilDischarger

elab_rules : command
| `(veil_discharger $id:ident $[for $target:ident]? := $proof:term) => do
  let name := id.getId.eraseMacroScopes
  let entries ← automaticDischargers.get
  if entries.any (·.name == name) then
    throwErrorAt id "discharger '{name}' is already registered"
  let appliesTo : VCMetadata → Bool ← match target with
    | none => pure (fun _ => true)
    | some t => match t.getId.eraseMacroScopes with
      | `induction => pure VCMetadata.isInduction
      | `trace => pure VCMetadata.isTrace
      | _ => throwErrorAt t "expected discharger target 'induction' or 'trace'"
  automaticDischargers.modify (·.push (.custom name appliesTo proof))

/-- Try the listed dischargers first. The remaining entries keep their relative order. -/
scoped elab "veil_discharger_order " "[" ids:rawIdent,* "]" : command => do
  let entries ← automaticDischargers.get
  let mut front := #[]
  for id in ids.getElems do
    let name := id.getId.eraseMacroScopes
    let some entry := entries.find? (·.name == name)
      | throwErrorAt id "unknown discharger '{name}'"
    if front.any (·.name == name) then
      throwErrorAt id "duplicate discharger '{name}' in order"
    front := front.push entry
  let rest := entries.filter fun e => !front.any (·.name == e.name)
  automaticDischargers.modify fun _ => front ++ rest

private def VCManager.addProofDischarger (mgr : VCManager VCMetadata SmtResult) (vcId : VCId)
    (label : Name) (term : Term) (reportFailure : Bool := false)
    (proof? : Option (TermElabM Witness) := none) : CommandElabM (VCManager VCMetadata SmtResult) := do
  let env ← Verifier.clearVerifierRuntime <$> getEnv
  mgr.mkAddDischarger vcId fun stmt id ch => do
    let id := { id with name := Name.mkSimple s!"{id.name}_{label}" }
    Discharger.fromTermWith term stmt id ch (quietOnUnknown := true) (proof? := proof?) fun _ data time => do
      -- An incomplete proof lets the manager continue to the next discharger.
      match data with
      | .inr ex =>
        unless reportFailure do return .unknown none time
        return .unknown (some (.unknown #[← ex.toMessageData.toString])) time
      | .inl witness =>
        let witness ← inlineFreshProofs env witness (rec := true)
        if witness.hasMVar || witness.hasFVar || witness.hasSorry then
          unless reportFailure do return .unknown none time
          let errors := (← Core.getMessageLog).toArray.filter (·.severity == .error)
          let reasons ← errors.mapM (·.data.toString)
          return .unknown (some (.unknown (if reasons.isEmpty then #["tactic did not produce a complete proof"] else reasons))) time
        return .proven (some witness) none time

/-- Attach the applicable automatic dischargers in the order active at VC generation. -/
def VCManager.addAutomaticDischargers (mgr : VCManager VCMetadata SmtResult) (vcId : VCId)
    (smt : VCStatement → DischargerIdentifier → Std.Channel (ManagerNotification VCMetadata SmtResult) →
      CommandElabM (Discharger SmtResult))
    (frame? : Option (Term × TermElabM Witness) := none) :
    CommandElabM (VCManager VCMetadata SmtResult) := do
  let some vc := mgr.nodes[vcId]? | return mgr
  let mut mgr := mgr
  for entry in ← automaticDischargers.get do
    match entry with
    | .frame =>
      if let some (term, build) := frame? then
        mgr ← mgr.addProofDischarger vcId `FRAME term (proof? := some build)
    | .smt => mgr ← mgr.mkAddDischarger vcId smt
    | .custom name appliesTo term =>
      if appliesTo vc.metadata then
        mgr ← mgr.addProofDischarger vcId name term (reportFailure := true)
  return mgr

end Veil
