import Veil.Frontend.DSL.Module.VCGen.Induction

open Lean Elab Command Veil

-- Synchronize cancellation with actual tactic execution, without timing races.
initialize gates : IO.Ref (Option (IO.Promise Unit × IO.Promise Unit)) ← IO.mkRef none
elab "await_cancellation" : tactic => do
  let some (entered, release) ← gates.get | throwError "missing test gates"
  entered.resolve ()
  let _ := (← IO.wait release.result?)
  Core.checkInterrupted

