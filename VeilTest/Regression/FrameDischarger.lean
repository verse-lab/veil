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

-- Compile the actual closed worker witnesses as theorems. Check their types
-- against the independently elaborated public VC statements.
open Lean Elab Command Veil in
run_cmd do
  let results ← Verifier.waitFilteredSync VCMetadata.isInduction
  for (name, expected) in [(`write_zero, "proven"), (`write_emptyLog, "proven"),
      (`reset_emptyLog, "proven"), (`reset_zero, "disproven"), (`write_noLive, "disproven")] do
    let some vc := results.vcs.find? (·.name == name) | throwError "missing {name}"
    unless vc.status.any (·.kindString == expected) do throwError "unexpected result {vc.status.map (·.kindString)} for {name}"
    let attempts := vc.timing.dischargers.filter (·.result.isSome)
    if expected == "disproven" then
      unless attempts.size == 2 && attempts[0]!.result.any (·.kindString == "unknown") &&
          attempts[1]!.result.any (·.kindString == "disproven") do
        throwError "expected framing to decline and SMT to find a counterexample for {name}"
    else
      unless attempts.size == 1 do throwError "unexpected fallback after framing {name}"
      unless vc.timing.dischargers[0]!.result.any (·.isSuccessful) && !vc.proofHasSorry do
        throwError "missing closed frame witness for {name}"
      let some (.proven (some proof) ..) := vc.timing.dischargers[0]!.result | throwError "missing proof"
      let mgr ← Verifier.readVCManager
      let statement ← liftTermElabM mgr.nodes[vc.id]!.toVCStatement.type
      let decl : TheoremVal := {
        name := (← getCurrNamespace) ++ name
        levelParams := []
        «type» := statement
        value := proof
      }
      liftCoreM <| addDecl (.thmDecl decl)

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
