module
public import Veil

veil module FrameDischarger

type node
individual counter : Nat
relation live : node → Bool
individual history : Nat

after_init { counter := 0; live N := false; history := 0 }
action write (n : node) {
  require counter = 0
  let m ← pick node
  require m = n
  live m := true
}
action reset { counter := 1 }
transition keep { counter' = counter }
invariant [bound] counter ≤ 2
invariant [zero] counter = 0
invariant [emptyLog] history = 0
invariant [noLive] ¬ live N

#gen_spec

open Lean Veil in
run_cmd do
  let mgr ← Verifier.readVCManager
  for (name, order) in [
      (`write_zero, #["FRAME", "WP"]), (`reset_emptyLog, #["FRAME", "WP"]),
      (`write_noLive, #["FRAME", "WP"]), (`reset_zero, #["FRAME", "WP"]),
      (`write_doesNotThrow, #["WP"]), (`initializer_emptyLog, #["FRAME", "WP"]),
      (`keep_zero, #["FRAME", "WP"]), (`keep_zero_tr, #["TR"]), (`write_zero_tr, #["TR"])] do
    let some vc := mgr.nodes.valuesArray.find? (·.name == name) | throwError "missing {name}"
    let actual := vc.dischargers.map fun d => (d.id.name.toString.splitOn "_").getLast!
    unless actual == order do throwError "unexpected order {actual} for {name}"

-- Exercise the public export path. A successful status alone does not require
-- a witness, and a kernel-accepted declaration can still depend on sorryAx.
set_option veil.printCounterexamples false

/-- noLive ... ❌ -/
#guard_msgs (substring := true) in
#check_action write

/-- zero ... ❌ -/
#guard_msgs (substring := true) in
#check_action reset

#gen_theorems

open Lean Elab Command Veil in
run_cmd do
  let mgr ← Verifier.readVCManager
  let results ← liftCoreM (mgr.toResults VCMetadata.isInduction)
  for (name, expected) in [(`write_bound, "proven"), (`write_zero, "proven"),
      (`write_emptyLog, "proven"), (`reset_noLive, "proven"), (`reset_emptyLog, "proven"),
      (`reset_zero, "disproven"), (`write_noLive, "disproven")] do
    let some vc := results.vcs.find? (·.name == name) | throwError "missing {name}"
    unless vc.status.any (·.kindString == expected) do throwError "unexpected result {vc.status.map (·.kindString)} for {name}"
    let fullName := (← getCurrNamespace) ++ name
    let attempts := vc.timing.dischargers.filter (·.result.isSome)
    if expected == "disproven" then
      unless attempts.size == 2 && attempts[0]!.result.any (·.kindString == "unknown") &&
          attempts[1]!.result.any (·.kindString == "disproven") do
        throwError "expected framing to decline and SMT to find a counterexample for {name}"
      if (← getEnv).contains fullName then throwError "exported a disproven VC: {fullName}"
    else
      let #[frame] := attempts | throwError "expected exactly one attempt for {name}"
      unless frame.name.toString.endsWith "_FRAME" do throwError "expected framing to prove {name}"
      let some (.proven (some proof) ..) := frame.result | throwError "missing frame witness for {name}"
      let .thmInfo thm ← getConstInfo fullName | throwError "expected a theorem for {fullName}"
      unless thm.value == proof do throwError "exported a different witness for {fullName}"
      let statement ← liftTermElabM mgr.nodes[vc.id]!.toVCStatement.type
      unless ← liftTermElabM (Meta.isDefEq thm.type statement) do
        throwError "exported theorem has the wrong statement for {fullName}"
      if (← collectAxioms fullName).contains ``sorryAx then
        throwError "exported theorem depends on sorryAx: {fullName}"

end FrameDischarger

veil module FrameDisabled

set_option veil.frame false
individual x : Nat
after_init { x := 0 }
action keep { pure () }
invariant [zero] x = 0
#gen_spec

open Veil in
run_cmd do
  let mgr ← Verifier.readVCManager
  for vc in mgr.nodes.valuesArray do
    if vc.dischargers.any (·.id.name.toString.endsWith "_FRAME") then
      throwError "framing is disabled but {vc.name} has a frame worker"

end FrameDisabled
