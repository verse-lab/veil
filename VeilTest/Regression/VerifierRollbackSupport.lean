module
public meta import Veil.Core.Tools.Verifier.TheoremDischarger
public meta import Veil.Core.Tools.Verifier.Server
public meta section
open Lean Elab Term Veil Veil.Verifier
initialize resetDuringValidation : IO.Ref Bool ← IO.mkRef false
elab "reset_during_validation_type" : term => do
  if ← resetDuringValidation.get then
    resetDuringValidation.set false
    let owner ← getVCManagerOwner
    let managerId := (← readVCManager)._managerId
    enqueue owner (.reset managerId)
  return mkConst ``True
