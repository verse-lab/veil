module

public import Veil
open Lean Meta Elab Command Veil

set_option veil.violationIsError false
set_option veil.deferVCGeneration true

veil module WPReplay

individual total : Nat
after_init { total := 0 }
action two {
  let left : Nat :| left > 1
  let right : Nat :| right > left
  total := left + right
}
action unused {
  let _discarded ← pick Bool
  total := 1
}
action throws {
  let bad : Nat :| bad > 0
  assert bad = 0
}
invariant [zero] total = 0
#gen_spec
/-- error: This assertion might fail when called from throws -/
#guard_msgs (error, drop info, drop warning) in
#check_invariants

run_cmd do
  let mod ← getCurrentModule
  let mut checked := #[]
  for vc in (← Verifier.waitFilteredSync (fun _ => true)).vcs do
    let .induction md := vc.metadata | continue
    unless md.style == .wp do continue
    let some model := vc.timing.dischargers.findSome? (fun d => match d.result with
      | some (.disproven (some (.sat ms)) _) => ms.findSome? id | _ => none) | continue
    let original ← mod.mkInvariantGoalVC (mkIdent md.action) (mkIdent md.property) .wp
    liftTermElabM do
      let w ← buildCounterexampleExprs model.raw mod md.action
      let check := checkInductionWitness mod original.toVCStatement md
      let expect (w : VeilCTI) (wanted : WitnessCheck) := do
        let got ← check w
        unless got == wanted do throwError "{md.action}: expected {repr wanted}, got {repr got}"
      unless model.structuredJson.getObjValD "witnessCheck" == toJson WitnessCheck.checked do
        throwError "{md.action}: {model.structuredJson.getObjValD "witnessCheck"}"
      if md.action == `two then
        let #[(_, a), (_, b)] := w.extraVals | throwError "expected both picks"
        expect { w with extraVals := w.extraVals.zipWith (fun (k, _) v => (k, v)) #[b,a] } .invalid
        let negative ← w.extraVals.mapM fun (k, v) => do
          return (k, if (← getExprName w.ctx k) == some `left then toExpr (-1 : Int) else v)
        expect { w with extraVals := negative } (.unverified "invalid Nat assignment left")
        let post ← Term.elabTermAndSynthesize (← `(⟨0⟩)) (some w.stateType)
        expect { w with postStateExpr := some post } .invalid
        let values ← witnessAssignments w.ctx w.extraVals
        let total ← mkAppM ``Nat.add #[← mkAppM ``Int.toNat #[values[`left]!], ← mkAppM ``Int.toNat #[values[`right]!]]
        let after ← Term.elabTermAndSynthesize (← `(⟨$(← Term.exprToSyntax total)⟩)) (some w.stateType)
        expect { w with postStateExpr := some after } .checked
      if md.action == `throws then
        let extraVals ← w.extraVals.mapM fun (k, v) => do
          let n ← getExprName w.ctx k
          return (k, if n == some (modelValueName `exception) then toExpr (-1 : Int) else v)
        expect { w with extraVals } .invalid
    checked := checked.push md.action
  unless checked.size == 3 && [`two, `unused, `throws].all checked.contains do
    throwError "expected WP failures for two, unused and throws, got {checked}"

end WPReplay
