module

public meta import Lean
public meta import Veil.Backend.SMT.Result
public meta import Veil.Frontend.DSL.Module.Names
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

open Lean Elab Term Command Lean.Parser.Term

namespace Veil

/-! ## Symbolic Transition Binders -/

/-- Quantify the action tag type and enumeration used by symbolic transitions. -/
def mkActionTagBinders (tagType : Ident) : TermElabM (Array (TSyntax ``bracketedBinder)) := do
  return #[← `(bracketedBinder| ($tagType : Type)),
    ← `(bracketedBinder| ($actionTagEnumInst : $(Ident.toEnumClass actionTagType) $tagType))]

/-- Preserve the spelling used by the trace decoder while preventing captures in user terms. -/
def mkTransitionTagBinder (tagType : Ident) (i : Nat) : TermElabM (Ident × TSyntax ``bracketedBinder) := do
  let tag := Lean.mkIdent <| modelBinderName (traceTagName i)
  return (tag, ← `(bracketedBinder| ($tag : $tagType)))

/-- The label constructor determines each argument type, including dependencies
on earlier arguments. Source parameter names are out of scope in this query. -/
def mkTransitionParamBinders (step action arity : Nat) :
    TermElabM (Array Ident × Array (TSyntax ``bracketedBinder)) := do
  let args ← (Array.range arity).mapM fun i => do
    let arg := Lean.mkIdent <| modelBinderName (traceArgumentName step action i)
    return (arg, ← `(bracketedBinder| ($arg : _)))
  return args.unzip

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

/-- Model names are assigned after elaboration. Changing a forall binder's
name here preserves every reference in its domain and body. -/
def nameModelBinders (type : Expr) (names : List (Option Name)) : Expr :=
  match type with
  | .forallE name domain body info =>
    .forallE (names.head?.join.getD (persistModelBinderName name))
      domain (nameModelBinders body (names.drop 1)) info
  | _ => type

def moduleModelNames (params : Array Parameter) : Array (Option Name) :=
  params.map fun p => if p.kind == .userParameter then some (modelParameterName p.name) else none

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
    (traceLabel : String := "discharger") (modelNames : Array (Option Name) := #[]) :
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
                let _ ← Smt.initAsyncState dischargerId.name (.some smtCh)
                let witness ← instantiateMVars $ ← withSynthesize (postpone := .no) $
                  withoutErrToSorry do
                    let goalType ← vcStatement.type
                    let goalType := nameModelBinders goalType modelNames.toList
                    elabTermEnsuringType term goalType
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

end Veil
