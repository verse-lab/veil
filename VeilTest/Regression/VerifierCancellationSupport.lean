module

public meta import Veil.Frontend.DSL.Module.VCGen.Common

public meta section
open Lean Elab Tactic
namespace VeilTest.VerifierCancellation

initialize gates : IO.Ref (Option (IO.Promise Unit × IO.Promise Unit)) ← IO.mkRef none

/-- A deterministic proof-elaboration checkpoint, released only after cancellation. -/
elab "cancellation_gate" : tactic => do
  let some (entered, release) ← gates.get | throwError "missing cancellation gates"
  entered.resolve ()
  let _ ← IO.wait release.result?
  Core.checkInterrupted

end VeilTest.VerifierCancellation
