import Veil

open Veil.ModelChecker
open Veil.ModelChecker.Simulation

/--
info: {"depth":0,"elapsed_ms":0,"max_traces":3,"result":{"explored_states":3,"result":"no_violation_found","termination_reason":{"condition":{"kind":"reached_trace_limit","max_traces":3},"kind":"early_termination"}},"seed":1,"traces_run":3}
-/
#guard_msgs in
#eval IO.println <| (Lean.toJson ({
  result := ModelCheckingResult.noViolationFound 3 (.earlyTermination (.reachedTraceLimit 3))
  tracesRun := 3
  maxTraces := 3
  elapsedMs := 0
  seed := 1
  depth := 0
} : SimulateResult Unit Unit Unit)).compress

/--
info: {"depth":0,"elapsed_ms":0,"explored_states":3,"max_traces":3,"result":"no_violation_found","seed":1,"termination_reason":{"condition":{"kind":"reached_trace_limit","max_traces":3},"kind":"early_termination"},"traces_run":3}
-/
#guard_msgs in
#eval IO.println <| (SimulateResult.toDisplayJson ({
  result := ModelCheckingResult.noViolationFound 3 (.earlyTermination (.reachedTraceLimit 3))
  tracesRun := 3
  maxTraces := 3
  elapsedMs := 0
  seed := 1
  depth := 0
} : SimulateResult Unit Unit Unit)).compress
