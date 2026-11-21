module

public import Veil

open Lean Meta Elab Command Veil
set_option veil.violationIsError false

veil module FiniteInduction
individual bit : Bool
individual gate : Bool
after_init { bit := false; gate := false }
action flip {
  require gate = true
  bit := true
}
invariant [off] bit = false
#gen_spec
#gen_executable
-- Only the closed gate is reachable, but induction also permits an open gate.
/-- info: ✅ No violation (explored 1 states) -/
#guard_msgs in
#model_check interpreted {} {}

#guard_msgs (drop info, drop warning) in
#check_invariants

def holds (s : State FieldConcreteType) : Bool :=
  decide (off (χ := FieldConcreteType) ({} : Theory) s)

def finiteOracle (bit gate bit' gate' : Bool) : Bool := Id.run do
  let th : Theory := {}
  let pre : State FieldConcreteType := ⟨bit, gate⟩
  let post : State FieldConcreteType := ⟨bit', gate'⟩
  let edges := ((enumerableTransitionSystem th).tr th pre).successes
  return holds pre && !holds post && edges.any (fun (l, s) => (l == Label.flip) && s == post)

run_cmd do
  let mod ← getCurrentModule
  let mut checked := 0
  for vc in (← Verifier.waitFilteredSync (fun _ => true)).vcs do
    let .induction md := vc.metadata | continue
    unless md.action == `flip && md.property == `off do continue
    let some model := vc.timing.dischargers.findSome? (fun d => match d.result with
      | some (.disproven (some (.sat ms)) _) => ms.findSome? id | _ => none) | throwError "missing SMT model"
    let original ← mod.mkInvariantGoalVC (mkIdent md.action) (mkIdent md.property) md.style
    liftTermElabM do
      let w ← buildCounterexampleExprs model.raw mod md.action
      let mut accepted : Nat := 0
      for b in Enumeration.allValues (α := Bool) do
        for g in Enumeration.allValues (α := Bool) do
          for b' in Enumeration.allValues (α := Bool) do
            for g' in Enumeration.allValues (α := Bool) do
              let state (x y : Bool) := mkAppOptM ``State.mk #[some w.stateType.appArg!, some (toExpr x), some (toExpr y)]
              let oracleExpr := mkAppN (mkConst ``finiteOracle) #[toExpr b, toExpr g, toExpr b', toExpr g']
              let expected ← unsafe evalExpr Bool (mkConst ``Bool) oracleExpr
              let got ← checkInductionWitness mod original.toVCStatement md
                { w with preStateExpr := ← state b g, postStateExpr := some (← state b' g') }
              unless got == (if expected then .checked else .invalid) do
                throwError "{md.style} ({b}, {g}) → ({b'}, {g'}): got {repr got}, expected violation = {expected}"
              if expected then accepted := accepted + 1
      unless accepted == 1 do throwError "wrong number of violations"
    checked := checked + 1
  unless checked == 2 do throwError "expected both styles"
end FiniteInduction
