module
public import Veil

veil module CustomDischargerProof

individual x : Nat
after_init { x := 0 }
action step { x := 0 }
invariant True
#gen_spec

section

-- Model a buggy tactic that assigns a closed proof of the wrong proposition.
open Lean Elab Tactic in
local elab "wrongProof" : tactic => liftMetaTactic fun goal => do
  goal.assign (mkConst ``True.intro)
  return []

veil_discharger wrongType for trace := by wrongProof
veil_discharger_order [wrongType, smt]

/-- error: No satisfying trace exists -/
#guard_msgs in
sat trace [wrongTypeRejected] { assert False }

end

section

set_option warn.sorry false in
sat trace [unfinished] { assert False } by sorry
sat trace [viaLemma] { assert False } by exact unfinished

veil_discharger unfinishedProof for trace := by exact viaLemma
veil_discharger_order [unfinishedProof, smt]

/-- error: No satisfying trace exists -/
#guard_msgs in
sat trace [sorryRejected] { assert False }

end

open Veil in
run_cmd do
  let mgr ← Verifier.readVCManager
  for (name, reason) in [(`wrongTypeRejected, "wrong type"), (`sorryRejected, "sorryAx")] do
    let some vc := mgr.nodes.valuesArray.find? (·.name == name) | throwError "missing {name}"
    let result : Option (DischargerResult SmtResult) := mgr._dischargerResults[(vc.uid, 0)]?
    let some (.unknown (some (.unknown reasons)) _) := result
      | throwError "expected the custom discharger to reject its proof for {name}"
    unless reasons.any (·.contains reason) do throwError "unexpected rejection for {name}: {reasons}"
    let fallback : Option (DischargerResult SmtResult) := mgr._dischargerResults[(vc.uid, 1)]?
    let some (.disproven ..) := fallback
      | throwError "expected SMT to disprove {name} after the custom discharger"

end CustomDischargerProof
