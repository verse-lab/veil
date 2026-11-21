module

public import Veil

public section

namespace TraceNormalizationDiagnostic

axiom assertion : Prop

open Lean in
simproc_decl failNormalization (assertion) := fun _ =>
  throwError "test normalization failure"

axiom unknownAssertion : Prop

-- Supply an unknown result through the solver's channel, then stop the tactic
-- as it would stop after an actual unknown result.
open Lean in
simproc_decl reportUnknown (unknownAssertion) := fun _ => do
  let state := Smt.asyncState.getState (← getEnv)
  let some channel := state.ch | throwError "missing trace SMT channel"
  Std.CloseableChannel.Sync.send channel
    ((state.name, state.index), .result (.unknown "test solver unknown reason"))
  throwError "synthetic unknown result"

end TraceNormalizationDiagnostic

veil module TraceNormalizationDiagnostic

individual flag : Bool

#gen_state

after_init { flag := false }
action set_flag { flag := true }
invariant True

#gen_spec

attribute [local nextSimp] TraceNormalizationDiagnostic.failNormalization

/--
error: BMC normalization failed before SMT
test normalization failure
-/
#guard_msgs in
sat trace {
  assert TraceNormalizationDiagnostic.assertion
}

attribute [local nextSimp] TraceNormalizationDiagnostic.reportUnknown

/--
error: Solver returned unknown
test solver unknown reason
-/
#guard_msgs in
sat trace {
  assert TraceNormalizationDiagnostic.unknownAssertion
}

end TraceNormalizationDiagnostic
