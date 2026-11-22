module

public import Veil

set_option warn.sorry false in
example : True := by
  set_option veil.smt.trust true in
  veil_smt

open Lean in
run_cmd do
  for src in ["veil_discharger exampleTac := by trivial", "veil_discharger_order [frame]"] do
    if (Parser.runParserCategory (← getEnv) `command src).isOk then
      throwError "command available outside the Veil scope: {src}"

section
open scoped Veil

/-- error: discharger 'frame' is already registered -/
#guard_msgs in
veil_discharger frame := by trivial

/-- error: expected discharger target 'induction' or 'trace' -/
#guard_msgs in
veil_discharger misspelled for inductions := by trivial

/-- error: unknown discharger 'missing' -/
#guard_msgs in
veil_discharger_order [missing]

/-- error: duplicate discharger 'smt' in order -/
#guard_msgs in
veil_discharger_order [smt, smt]

end

veil module NamedDischargers

set_option veil.deferVCGeneration true
individual x : Nat
after_init { x := 0 }
action step { x := 0 }
transition keep { x' = x }
invariant [zero] x = 0
invariant [constant] True
#gen_spec

veil_discharger traceOnly for trace := by fail "trace only"

veil_discharger arithmetic for induction := by
  unveil <;> omega

veil_discharger_order [arithmetic, smt, frame]
#check_invariants

run_cmd do
  let _ ← Veil.Verifier.waitFilteredSync (·.isInduction)
  let mgr ← Veil.Verifier.readVCManager
  let some step := mgr.nodes.valuesArray.find? (·.name == `step_zero) | throwError "missing step VC"
  unless step.successful == some 0 do throwError "arithmetic did not prove step_zero"
  for name in [`step_zero, `step_zero_tr, `step_doesNotThrow, `keep_zero_tr, `keep_zero] do
    unless mgr.nodes.valuesArray.any (·.name == name) do throwError "missing VC {name}"
  for vc in mgr.nodes.valuesArray do
    let labels := vc.dischargers.map (·.id.name.toString)
    let expected := if Veil.Verifier.isDoesNotThrow vc.metadata then #["arithmetic", "WP"]
      else if vc.name.toString.endsWith "_tr" then #["arithmetic", "TR"]
      else #["arithmetic", "WP", "FRAME"]
    unless labels.map (fun n => (n.splitOn "_").getLast!) == expected do
      throwError "unexpected induction dischargers: {labels}"

-- A SAT proof supplies the actual existential witness without involving a solver.
section
sat trace [firstWitness] { } by
  refine ⟨ActionTag_IndT, inferInstance, ⟨⟩, ⟨0⟩, ?_⟩
  simp [nextSimp, smtSimp]
  rfl

veil_discharger witness for trace := by exact firstWitness
veil_discharger skip := by fail "intentionally inconclusive"
local macro "preferWitness" : command => `(veil_discharger_order [skip, witness])
preferWitness

/-- info: Proved that a satisfying trace exists -/
#guard_msgs in
sat trace [byWitness] { }

run_cmd do
  let mgr ← Veil.Verifier.readVCManager
  let some vc := mgr.nodes.valuesArray.find? (·.name == `byWitness) | throwError "missing trace"
  let labels := vc.dischargers.map (·.id.name.toString)
  unless labels.size == 4 && labels[0]!.endsWith "_skip" && labels[1]!.endsWith "_witness" &&
      labels[3]!.endsWith "_traceOnly" && vc.successful == some 1 do
    throwError "unexpected trace dischargers: {labels}, successful: {vc.successful}"
  let result : Option (Veil.DischargerResult Veil.SmtResult) := mgr._dischargerResults[(vc.uid, 0)]?
  let some (.unknown (some (.unknown reasons)) _) := result
    | throwError "custom tactic failure lost its reason"
  unless reasons.any (·.contains "intentionally inconclusive") do
    throwError "missing custom tactic diagnostics: {reasons}"

#gen_theorems
open Lean in
run_cmd do
  let some (.thmInfo thm) := (← getEnv).find? ``byWitness | throwError "missing trace theorem"
  unless thm.value.getUsedConstants.contains ``firstWitness do throwError "unexpected custom witness"

end

#guard_msgs (drop info) in
sat trace [afterScope] { }

run_cmd do
  let mgr ← Veil.Verifier.readVCManager
  let some vc := mgr.nodes.valuesArray.find? (·.name == `afterScope) | throwError "missing trace"
  unless vc.dischargers.size == 2 && vc.dischargers[1]?.any (·.id.name.toString.endsWith "_traceOnly") do
    throwError "trace dischargers escaped their section"

end NamedDischargers

veil module FrameAfterMiss

individual counter : Nat
individual history : Nat
after_init { counter := 0; history := 0 }
action lower { counter := counter - 1 }
invariant [bounded] counter ≤ 10
invariant [emptyLog] history = 0

veil_discharger miss for induction := by fail "try next"
veil_discharger_order [miss, frame]
#gen_spec

open Veil in
run_cmd do
  let results ← Verifier.waitFilteredSync VCMetadata.isInduction
  let some vc := results.vcs.find? (·.name == `lower_emptyLog) | throwError "missing frame VC"
  let attempts := vc.timing.dischargers.filter (·.result.isSome)
  let names := attempts.map (fun d => (d.name.toString.splitOn "_").getLast!)
  unless names == #["miss", "FRAME"] && attempts.back!.result.any (·.isSuccessful) && !vc.proofHasSorry do
    throwError "expected frame to prove the goal after the custom miss, got {names}"

end FrameAfterMiss
