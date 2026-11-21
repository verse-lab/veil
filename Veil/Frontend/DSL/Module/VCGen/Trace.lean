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
public meta import Veil.Frontend.DSL.Module.VCGen.Replay

public meta section

/-!
# Trace VC Generation

This module provides dischargers for symbolic trace queries (`sat trace` / `unsat trace`).
It integrates trace verification with the VCManager infrastructure.
-/

open Lean Elab Term Command

namespace Veil

/-! ## Trace-Specific Result Processing -/

/-- The positive trace query, quantified over its module parameters, theory,
states and labels. Both trace commands check the same proposition on SAT. -/
structure TraceReplay where
  params : Array Parameter
  statement : Term
  numTransitions : Nat

def TraceReplay.check (query : TraceReplay) (w : VeilTrace) : TermElabM WitnessCheck :=
  checkWitness do
    unless w.stateExprs.size == query.numTransitions + 1 && w.labelExprs.size == query.numTransitions do
      return mkConst ``False
    let template ← elabTermAndSynthesize query.statement (some (.sort .zero))
    let body ← specializeWitnessModule template query.params w.theoryType w.stateType w.enumAdapts
      (← witnessAssignments w.ctx w.extraVals)
    specializeWitness body (#[w.theoryExpr] ++ w.stateExprs ++ w.labelExprs)

/-- Process SMT outputs and build trace counterexamples on SAT.
    Unlike the standard `overallSmtResult`, this uses `buildTraceFromModel` for trace queries. -/
private def overallSmtResultForTrace (query : TraceReplay) (isExpectedSat : Bool)
    (outputs : Array SmtOutput) : TermElabM (Option SmtResult) := do
  let mod ← getCurrentModule
  buildSmtResult outputs (fun sat => do
    sat.filterMapM (fun ce => return ← ce.mapM (fun ce => do
      try
        -- Build trace from model instead of single-step counterexample
        let veilTrace ← buildTraceFromModel ce mod query.numTransitions
        -- Convert to ModelCheckingResult-like JSON for TraceDisplayViewer
        let structuredJson : Json ← unsafe veilTrace.toModelCheckingResultJson isExpectedSat
        let structuredJson := structuredJson.setObjVal! "witnessCheck" (toJson (← query.check veilTrace))
        return .some { raw := ce, rawHtml := ← renderSmtModel ce, structuredJson := structuredJson }
      catch ex =>
        dbg_trace "Failed to build trace counterexample; exception: {← ex.toMessageData.toString}"
        return none)))

/-! ## Trace Discharger -/

/-- Create a DischargerResult from SMT outputs for trace queries.
    - `sat trace`: expects SAT (trace exists), UNSAT means no such trace
    - `unsat trace`: expects UNSAT (no such trace), SAT is a counterexample
    If `ex?` is provided and no SMT result is available, returns an error with the exception. -/
private def mkTraceDischargerResult (expectedName : Name) (query : TraceReplay) (isExpectedSat : Bool)
    (ch : Std.CloseableChannel ((Name × Nat) × Smt.AsyncOutput))
    (time : Nat) (ex? : Option Exception := none) : TermElabM (DischargerResult SmtResult) := do
  let outputs ← collectSmtOutputs ch expectedName
  let result ← overallSmtResultForTrace query isExpectedSat outputs
  match result with
  | .none => match ex? with
    | some ex =>
      match ← unknownReasonFromException? ex with
      | some reason => return .unknown (.some (.unknown #[reason])) time
      | none => return .error #[(ex, s!"{← ex.toMessageData.toString}")] time
    | none => return .proven none .none time
  | .some (.error exs) => return .error exs time
  | .some (.unknown _) => return .unknown result time
  | .some r@(.sat _) | .some r@(.unsat _) =>
    return if (r matches .sat _) == isExpectedSat then .proven none r time else .disproven r time

/-- Create a discharger for trace queries that doesn't require an external proof term.

    This discharger generates an internal SMT tactic and evaluates it against the goal.
    The tactic simplifies the goal and calls SMT. Results are collected from the async channel.

    Parameters:
    - `query`: The positive query used to replay a decoded trace
    - `isExpectedSat`: True for `sat trace`, false for `unsat trace`
    - `vcStatement`: The VC statement to check
    - `dischargerId`: Identifier for this discharger
    - `ch`: Channel to communicate with VCManager
    - `cancelTk?`: Optional cancellation token
-/
def TraceDischarger.fromAssertion (query : TraceReplay) (isExpectedSat : Bool)
    (vcStatement : VCStatement) (dischargerId : DischargerIdentifier)
    (ch : Std.Channel (ManagerNotification VCMetadata SmtResult))
    (_cancelTk? : Option IO.CancelToken := none) : CommandElabM (Discharger SmtResult) := do
  let smtTactic ← `(term| by veil_bmc)
  Discharger.fromTermWith smtTactic vcStatement dischargerId ch
    (traceLabel := "trace discharger") (modelNames := moduleModelNames query.params) fun smtCh data time =>
    -- Trace queries don't require the elaborated witness to be complete — the
    -- SMT result is what matters — so the witness is dropped and only an
    -- elaboration exception is surfaced.
    mkTraceDischargerResult dischargerId.name query isExpectedSat smtCh
      time (ex? := data.getRight?)

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
