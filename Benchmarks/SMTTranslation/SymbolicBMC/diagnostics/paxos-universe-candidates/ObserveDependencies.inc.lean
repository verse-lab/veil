/- Diagnostic-only translator: observes selected residuals and returns none,
   leaving production translation behavior unchanged. Prepared, not run. -/

open Lean Meta

@[smt_translate]
meta def issue123ObserveComputationalDependencies : Smt.Translator := fun e => do
  if e.isAppOfArity ``decide 2 then
    logInfo m!"ISSUE123_RESIDUAL_DECIDE: {e}"
  if e.isLambda then
    logInfo m!"ISSUE123_RESIDUAL_LAMBDA: {e}"
  if let .const name levels := e then
    if name == ``DecidableEq then
      let info ← getConstInfo name
      logInfo m!"ISSUE123_INCOMING_DECIDABLE_EQ: levels={repr levels}, declared={info.levelParams}"
      try
        let ty ← inferType e
        logInfo m!"ISSUE123_VALID_DECIDABLE_EQ: type={ty}"
      catch ex =>
        logInfo m!"ISSUE123_ALREADY_INVALID_DECIDABLE_EQ: {ex.toMessageData}"
  return none
