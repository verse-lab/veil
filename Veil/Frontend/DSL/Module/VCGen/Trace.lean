module

public meta import Lean
public meta import Veil.Frontend.DSL.Module.Representation
public meta import Veil.Frontend.DSL.Module.Util
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Frontend.DSL.Infra.Metadata
public meta import Veil.Util.Meta
public meta import Veil.Core.Tools.Verifier.Server
public meta import Veil.Frontend.DSL.Tactic
public meta import Veil.Core.UI.Verifier.Model
public meta import Veil.Core.UI.Verifier.TraceCounterexample
public meta import Veil.Frontend.DSL.Module.VCGen.Common

public meta section

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
    A Lean proof of the SMT query also establishes UNSAT if preprocessing closes it. -/
private def mkTraceDischargerResult [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT BaseIO m]
    [MonadLiftT (EIO Std.CloseableChannel.Error) m] [MonadLiftT MetaM m]
    (expectedName : Name) (numTransitions : Nat) (isExpectedSat : Bool)
    (ch : Std.CloseableChannel ((Name × Nat) × Smt.AsyncOutput))
    (data : Witness ⊕ Exception) (time : Nat) : m (DischargerResult SmtResult) := do
  let outputs ← collectSmtOutputs ch expectedName
  let result ← overallSmtResultForTrace numTransitions isExpectedSat outputs
  match result with
  | .none => match data with
    | .inr ex =>
      match ← unknownReasonFromException? ex with
      | some reason => return .unknown (.some (.unknown #[reason])) time
      | none => return .error #[(ex, s!"{← ex.toMessageData.toString}")] time
    | .inl witness =>
      if witness.hasMVar || witness.hasFVar || witness.hasSorry then return .unknown none time
      return if isExpectedSat then .disproven none time else .proven none none time
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
    - `smtQuery`: The universal negation used for countermodel search
    - `vcStatement`: The VC registered with the manager
    - `dischargerId`: Identifier for this discharger
    - `ch`: Channel to communicate with VCManager
    - `cancelTk?`: Optional cancellation token
-/
def TraceDischarger.fromAssertion (numTransitions : Nat) (isExpectedSat : Bool) (smtQuery : Term)
    (vcStatement : VCStatement) (dischargerId : DischargerIdentifier)
    (ch : Std.Channel (ManagerNotification VCMetadata SmtResult))
    (_cancelTk? : Option IO.CancelToken := none) : CommandElabM (Discharger SmtResult) := do
  let smtTactic ← `(term| by veil_bmc)
  let discharger ← Discharger.fromTermWith smtTactic { vcStatement with statement := smtQuery }
    dischargerId ch (traceLabel := "trace discharger") fun smtCh data time =>
      mkTraceDischargerResult dischargerId.name numTransitions isExpectedSat smtCh data time
  -- For SAT the tactic runs against a different goal and cannot be replayed
  -- as a proof of the existential statement.
  return if isExpectedSat then { discharger with term := none } else discharger

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
