import VeilTest.ActionExecution

open Lean Elab Term Meta

namespace VeilTest.ActionExecution.MetaHardening

abbrev zeroAlias : Nat := 0

def dependentApp (n : Nat) (i : Fin (n + 1)) : Nat := i.val

def aliasIndex : Fin (zeroAlias + 1) := ⟨0, by simp [zeroAlias]⟩
def zeroIndex : Fin (0 + 1) := ⟨0, by simp⟩

theorem dependentLeft :
    dependentApp zeroAlias aliasIndex = dependentApp zeroAlias aliasIndex := rfl

theorem dependentRight :
    dependentApp 0 zeroIndex = dependentApp 0 zeroIndex := rfl

/- A healer fallback must remain total when congruence would have to vary an
argument on which a later argument's type depends. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let joined ← Meta.mkEqTrans (mkConst ``dependentLeft) (mkConst ``dependentRight)
  let healed ← try
    Veil.Simp.healEqTransJunctions joined
  catch ex =>
    throwError "dependent equality junction escaped the healer: {ex.toMessageData}"
  Meta.check healed

end VeilTest.ActionExecution.MetaHardening
