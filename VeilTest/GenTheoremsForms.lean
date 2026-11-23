module

public import Veil

set_option veil.smt.trust false
set_option linter.unusedVariables false

open Lean in
private meta def checkForms (ns : Name) (names : Array Name) : Elab.Command.CommandElabM Unit := do
  for name in names do
    let name := ns ++ name
    unless (← getEnv).find? name matches some (.thmInfo _) do
      throwError "expected theorem {name}"
    if (← collectAxioms name).contains ``sorryAx then
      throwError "unexpected sorryAx in {name}"

veil module InvariantForms

type node
relation marked : node → Bool
after_init { marked N := true }
action write (n : node) { marked n := true }
transition keep (n : node) { ∀ N, marked' N ↔ marked N }
action trFallback (n : node) { marked n := true }
transition wpFallback (n : node) { ∀ N, marked' N ↔ marked N }
action unchecked { pure () }
invariant [all_marked] marked N = true
#gen_spec

#check_action write
#check_action keep
#gen_theorems

run_cmd checkForms `InvariantForms #[
  `write_all_marked, `write_all_marked_tr, `keep_all_marked, `keep_all_marked_tr]

run_cmd do
  let mgr ← Veil.Verifier.readVCManager
  for name in [`write_all_marked_tr, `keep_all_marked] do
    let some vc := mgr.nodes.valuesArray.find? (·.name == name) | throwError "missing {name}"
    unless mgr.dormantVCs.contains vc.uid && vc.dischargers.all (·.task.isNone) do
      throwError "publishing the companion started its solver: {name}"

#guard_msgs in
#gen_theorems

-- Make each primary return unknown. Only its fallback can supply the witness.
run_cmd do
  Veil.Verifier.withVCManager fun ref => do
    let mut mgr ← ref.get
    for name in [`trFallback_all_marked, `wpFallback_all_marked_tr] do
      let some vc := mgr.nodes.valuesArray.find? (·.name == name) | throwError "missing {name}"
      for d in vc.dischargers do
        let result : Veil.DischargerResult Veil.SmtResult := .unknown none 0
        d.resultPromise.resolve result
        mgr ← mgr.recordDischargerResult d.id result
    ref.set mgr

#check_action trFallback
#check_action wpFallback
end InvariantForms

run_cmd checkForms `InvariantForms #[
  `trFallback_all_marked, `trFallback_all_marked_tr, `wpFallback_all_marked, `wpFallback_all_marked_tr]

run_cmd do
  for name in [`InvariantForms.unchecked_all_marked, `InvariantForms.unchecked_all_marked_tr] do
    if (← Lean.getEnv).contains name then throwError "unexpected unrequested theorem {name}"

veil module DegenerateTransitionTheorems

relation marked : Bool
#gen_state
after_init { marked := true }
transition keep { True }
transition blocked { False }
invariant [trivial_inv] True
#gen_spec
#check_invariants
#gen_theorems

run_cmd checkForms `DegenerateTransitionTheorems #[
  `initializer_trivial_inv, `initializer_trivial_inv_tr, `keep_trivial_inv, `keep_trivial_inv_tr, `blocked_trivial_inv, `blocked_trivial_inv_tr]

end DegenerateTransitionTheorems

veil module PublishedTheoremConflict

relation marked : Bool
#gen_state
after_init { marked := true }
action keep { pure () }
invariant [all_marked] marked
#gen_spec

#guard_msgs (drop info) in
#check_invariants

theorem keep_all_marked_tr : True := True.intro

/--
error: cannot generate VC theorem `PublishedTheoremConflict.keep_all_marked_tr` because a declaration with that name already exists with a different type
-/
#guard_msgs in
#gen_theorems

end PublishedTheoremConflict
