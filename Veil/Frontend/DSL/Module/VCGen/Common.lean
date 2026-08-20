import Lean
import Veil.Backend.SMT.Result
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Core.Tools.Verifier.Server
import Veil.Core.UI.Verifier.Model

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
    (traceLabel : String := "discharger") : CommandElabM (Discharger SmtResult) := do
  let cancelTk ← IO.CancelToken.new
  let smtCh ← Std.CloseableChannel.new
  -- Create promises to track start time and result
  let startTimePromise ← IO.Promise.new
  let resultPromise ← IO.Promise.new
  -- Use wrapAsyncAsSnapshot for proper snapshot tree integration with the language server
  let mk ← Command.wrapAsyncAsSnapshot (fun vcStatement : VCStatement => do
    -- Resolve the start time promise when the discharger actually begins
    let startTime ← IO.monoMsNow
    startTimePromise.resolve startTime
    let res ← (do
      try
        -- Wrap in profiler trace for discharger timing
        withTraceNode (`veil.perf.discharger ++ dischargerId.name)
            (fun _ => return s!"{traceLabel} {dischargerId.name}") do
          liftTermElabM $ do
            let _ ← Smt.initAsyncState dischargerId.name (.some smtCh)
            let witness ← instantiateMVars $ ← withSynthesize (postpone := .no) $
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
    publishDischargerResult resultPromise ch dischargerId res
  ) cancelTk
  -- Dedicated thread: the task blocks in in-process solver FFI for its whole
  -- duration, which would starve the bounded elaboration thread pool
  let mkTask := (mk vcStatement).asTask (prio := .dedicated)
  return {
    id := dischargerId,
    term := term,
    cancelTk := cancelTk,
    task := Option.none,
    startTimePromise := startTimePromise,
    resultPromise := resultPromise,
    mkTask := mkTask
  }

end Veil
