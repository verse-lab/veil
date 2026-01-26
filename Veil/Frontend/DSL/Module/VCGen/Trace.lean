import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Infra.Metadata
import Veil.Util.Meta
import Veil.Core.Tools.Verifier.Server
import Veil.Frontend.DSL.Tactic
import Veil.Core.UI.Verifier.Model
import Veil.Core.UI.Verifier.TraceCounterexample
import Veil.Frontend.DSL.Module.VCGen.Common

/-!
# Trace VC Generation

This module provides dischargers for symbolic trace queries (`sat trace` / `unsat trace`).
It integrates trace verification with the VCManager infrastructure.
-/

open Lean Elab Term Command

namespace Veil

/-! ## Trace-Specific Result Processing -/

/-- Process SMT outputs and build trace counterexamples on SAT.
    Unlike the standard `overallSmtResult`, this uses `buildTraceFromModel` for trace queries. -/
private def overallSmtResultForTrace [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT BaseIO m]
    [MonadLiftT MetaM m] (numTransitions : Nat) (isExpectedSat : Bool)
    (outputs : Array SmtOutput) : m (Option SmtResult) := do
  let mod ← getCurrentModule
  buildSmtResult outputs (fun sat => do
    sat.filterMapM (fun ce => return ← ce.mapM (fun ce => do
      try
        -- Build trace from model instead of single-step counterexample
        let veilTrace ← buildTraceFromModel ce mod numTransitions
        -- Convert to ModelCheckingResult-like JSON for TraceDisplayViewer
        let structuredJson : Json ← unsafe veilTrace.toModelCheckingResultJson isExpectedSat
        return .some { raw := ce, rawHtml := ← renderSmtModel ce, structuredJson := structuredJson }
      catch ex =>
        dbg_trace "Failed to build trace counterexample; exception: {← ex.toMessageData.toString}"
        return none)))

/-! ## Trace Discharger -/

/-- Create a DischargerResult from SMT outputs for trace queries.
    - `sat trace`: expects SAT (trace exists), UNSAT means no such trace
    - `unsat trace`: expects UNSAT (no such trace), SAT is a counterexample
    If `ex?` is provided and no SMT result is available, returns an error with the exception. -/
private def mkTraceDischargerResult [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT BaseIO m]
    [MonadLiftT (EIO Std.CloseableChannel.Error) m] [MonadLiftT MetaM m]
    (expectedName : Name) (numTransitions : Nat) (isExpectedSat : Bool)
    (ch : Std.CloseableChannel ((Name × Nat) × Smt.AsyncOutput))
    (time : Nat) (ex? : Option Exception := none) : m (DischargerResult SmtResult) := do
  let outputs ← collectSmtOutputs ch expectedName
  let result ← overallSmtResultForTrace numTransitions isExpectedSat outputs
  match result with
  | .none => match ex? with
    | some ex => return .error #[(ex, s!"{← ex.toMessageData.toString}")] time
    | none => return .proven none .none time
  | .some (.error exs) => return .error exs time
  | .some (.unknown _) => return .unknown result time
  | .some r@(.sat _) | .some r@(.unsat _) =>
    return if (r matches .sat _) == isExpectedSat then .proven none r time else .disproven r time

/-- Create a discharger for trace queries that doesn't require an external proof term.

    This discharger generates an internal SMT tactic and evaluates it against the goal.
    The tactic simplifies the goal and calls SMT. Results are collected from the async channel.

    Parameters:
    - `numTransitions`: Number of transitions in the trace
    - `isExpectedSat`: True for `sat trace`, false for `unsat trace`
    - `vcStatement`: The VC statement to check
    - `dischargerId`: Identifier for this discharger
    - `ch`: Channel to communicate with VCManager
    - `cancelTk?`: Optional cancellation token
-/
def TraceDischarger.fromAssertion (numTransitions : Nat) (isExpectedSat : Bool)
    (vcStatement : VCStatement) (dischargerId : DischargerIdentifier)
    (ch : Std.Channel (ManagerNotification VCMetadata SmtResult))
    (_cancelTk? : Option IO.CancelToken := none) : CommandElabM (Discharger SmtResult) := do
  -- let cancelTk := cancelTk?.getD $ (Context.cancelTk? (← read)).getD (← IO.CancelToken.new)
  let cancelTk ← IO.CancelToken.new
  let smtCh ← Std.CloseableChannel.new
  -- Generate an internal tactic that uses veil_smt which handles SMT configuration
  let smtTactic ← `(term| by veil_bmc)
  -- Create promises to track start time and result
  let startTimePromise ← IO.Promise.new
  let resultPromise ← IO.Promise.new
  -- Use wrapAsyncAsSnapshot for proper snapshot tree integration with the language server
  let mk ← Command.wrapAsyncAsSnapshot (fun vcStatement : VCStatement => do
    -- Wrap in profiler trace for discharger timing
    withTraceNode (`veil.perf.discharger ++ dischargerId.name)
        (fun _ => return s!"trace discharger {dischargerId.name}") do
      let res ← (do
        -- Resolve the start time promise when the discharger actually begins
        let startTime ← IO.monoMsNow
        startTimePromise.resolve startTime
        try
          liftTermElabM $ do
            let _ ← Smt.initAsyncState dischargerId.name (.some smtCh)
            -- Elaborate the tactic against the goal type (same pattern as Induction.lean)
            -- We don't need the witness for trace queries, just the SMT result
            let _ ← instantiateMVars $ ← withSynthesize (postpone := .no) $
              withoutErrToSorry $ elabTermEnsuringType smtTactic (← vcStatement.type)
            let endTime ← IO.monoMsNow
            -- For trace queries, we don't require the witness to be complete
            -- The SMT result is what matters
            let dischargerResult ← mkTraceDischargerResult dischargerId.name numTransitions
              isExpectedSat smtCh (endTime - startTime)
            return dischargerResult
        catch ex =>
          let endTime ← IO.monoMsNow
          liftTermElabM $ mkTraceDischargerResult dischargerId.name numTransitions
            isExpectedSat smtCh (endTime - startTime) (ex? := some ex)
        finally
          if ← cancelTk.isSet then
            pure ()
      )
      -- Resolve the result promise so Discharger.status can read it
      resultPromise.resolve res
      -- Send notification to manager
      let _ ← ch.send (.dischargerResult dischargerId res)
      -- Note: wrapAsyncAsSnapshot expects Unit, so no return value
  ) cancelTk
  let mkTask := (mk vcStatement).asTask
  return {
    id := dischargerId,
    term := smtTactic,
    cancelTk := cancelTk,
    task := Option.none,
    startTimePromise := startTimePromise,
    resultPromise := resultPromise,
    mkTask := mkTask
  }

/-! ## Trace VC Statement Building -/

/-- Create a VCStatement for a trace query.

    The statement is either:
    - For `sat trace`: `∃ binders..., conjunction` (existential)
    - For `unsat trace`: `∀ binders..., ¬conjunction` (universal negation)
-/
def mkTraceVCStatement (_mod : Module) (name : Name) (statement : Term)
    : CommandElabM VCStatement := do
  let params := #[]  -- Trace VCs don't have external parameters
  return {
    name := name
    params := params
    statement := statement
  }

/-- Create VCMetadata for a trace query. -/
def mkTraceVCMetadata (isExpectedSat : Bool) (numTransitions : Nat)
    (traceName : Option Name := none) (assertion : Option Term := none) : VCMetadata :=
  .trace {
    isExpectedSat := isExpectedSat
    numTransitions := numTransitions
    traceName := traceName
    assertion := assertion
  }

end Veil
