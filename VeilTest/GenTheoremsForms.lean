module

public import Veil

public section

set_option veil.smt.trust false
set_option linter.unusedVariables false

open Lean in
meta def checkPublishedVCTheorems (ns : Name) (names : Array Name) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  for name in names do
    let fullName := ns ++ name
    let some info := env.find? fullName
      | throwError "expected theorem {fullName} in the main environment"
    let axioms ← collectAxioms fullName
    -- Module imports expose theorem signatures as axiomInfo, with separately
    -- recorded proof provenance. Locally, require an actual theorem declaration.
    unless (info matches .thmInfo _) ||
        ((info matches .axiomInfo _) && (env.getModuleIdxFor? fullName).isSome &&
          !axioms.contains fullName) do
      throwError "expected a proved theorem {fullName}"
    if axioms.contains ``sorryAx then
      throwError "unexpected sorry in {fullName}"

veil module PublishedWPTheorems

type node
relation marked : node → Bool
#gen_state

after_init {
  marked N := true
}

action keep (n : node) {
  marked n := true
}

invariant [all_marked] marked N = true

#gen_spec

#guard_msgs (drop info) in
#check_invariants
#gen_theorems

-- Both forms and exception-freedom proofs are published by #gen_theorems.
run_cmd checkPublishedVCTheorems `PublishedWPTheorems #[
  `initializer_doesNotThrow, `initializer_all_marked, `initializer_all_marked_tr,
  `keep_doesNotThrow, `keep_all_marked, `keep_all_marked_tr]

-- No solver work was added for the dormant transition-form alternative.
run_cmd do
  let mgr ← Veil.Verifier.vcManager.atomically fun ref => ref.get
  for (_, vc) in mgr.nodes.toArray do
    if vc.name == `keep_all_marked_tr then
      unless vc.successful.isNone do
        throwError "expected the transition theorem to be derived without running its discharger"

#guard_msgs (drop info) in
#check_invariants
#gen_theorems
#gen_theorems

end PublishedWPTheorems

veil module PublishedTRTheorems

type node
relation marked : node → Bool
#gen_state

after_init {
  marked N := true
}

transition keep (n : node) {
  ∀ N, marked' N ↔ marked N
}

invariant [all_marked] marked N = true

#gen_spec

#guard_msgs (drop info) in
#check_invariants
#gen_theorems

-- Transition syntax uses TR first, so this also tests the reverse bridge.
run_cmd checkPublishedVCTheorems `PublishedTRTheorems #[
  `initializer_doesNotThrow, `initializer_all_marked, `initializer_all_marked_tr,
  `keep_doesNotThrow, `keep_all_marked, `keep_all_marked_tr]

run_cmd do
  let mgr ← Veil.Verifier.vcManager.atomically fun ref => ref.get
  for (_, vc) in mgr.nodes.toArray do
    if vc.name == `keep_all_marked then
      unless vc.successful.isNone do
        throwError "expected the WP theorem to be derived without running its discharger"

end PublishedTRTheorems

veil module InteractiveTRTheorems

relation marked : Bool
#gen_state
after_init { marked := true }
action keep { pure () }
invariant [all_marked] marked
#gen_spec

-- Supply an interactive proof of the dormant TR alternative of an ordinary
-- action. Its WP theorem must be derived from this proof, without rerunning SMT.
open Lean Elab Command in
run_cmd do
  let mgr ← Veil.Verifier.vcManager.atomically fun ref => ref.get
  let some (_, vc) := mgr.nodes.toArray.find? (fun (_, vc) => vc.name == `keep_all_marked_tr)
    | throwError "missing transition VC"
  elabCommand (← `(command| @[veil] theorem $(mkIdent vc.name) $(vc.params)* :
    $(vc.statement) := by veil_solve_tr))

-- Model the other automatic discharger returning unknown, so publication must
-- use the interactive witness of its alternative.
run_cmd do
  Veil.Verifier.withVCManager fun ref => do
    let mut mgr ← ref.get
    let some (_, vc) := mgr.nodes.toArray.find? (fun (_, vc) => vc.name == `keep_all_marked)
      | throwError "missing automatic VC"
    for d in vc.dischargers do
      let result : Veil.DischargerResult Veil.SmtResult := .unknown none 0
      d.resultPromise.resolve result
      mgr ← mgr.recordDischargerResult d.id result
    ref.set mgr

#gen_theorems

run_cmd checkPublishedVCTheorems `InteractiveTRTheorems #[`keep_all_marked, `keep_all_marked_tr]

run_cmd do
  let mgr ← Veil.Verifier.vcManager.atomically fun ref => ref.get
  for (id, vc) in mgr.nodes.toArray do
    if vc.name == `keep_all_marked then
      unless (mgr.provenWitness? id).isNone do
        throwError "expected the WP theorem to use the interactive TR proof"

end InteractiveTRTheorems

veil module InteractiveWPTransitionTheorems

type node
relation marked : node → Bool
#gen_state
after_init { marked N := true }
transition keep (n : node) { ∀ N, marked' N ↔ marked N }
invariant [all_marked] marked N = true
#gen_spec

-- Exercise the WP fallback for a native transition, including the fact that
-- its postcondition depends only on the module's part of the ambient state.
open Lean Elab Command in
run_cmd do
  let mgr ← Veil.Verifier.vcManager.atomically fun ref => ref.get
  let some (_, vc) := mgr.nodes.toArray.find? (fun (_, vc) => vc.name == `keep_all_marked)
    | throwError "missing WP VC"
  elabCommand (← `(command| @[veil] theorem $(mkIdent vc.name) $(vc.params)* :
    $(vc.statement) := by veil_solve_wp))

-- Model the other automatic discharger returning unknown, so publication must
-- use the interactive witness of its alternative.
run_cmd do
  Veil.Verifier.withVCManager fun ref => do
    let mut mgr ← ref.get
    let some (_, vc) := mgr.nodes.toArray.find? (fun (_, vc) => vc.name == `keep_all_marked_tr)
      | throwError "missing automatic VC"
    for d in vc.dischargers do
      let result : Veil.DischargerResult Veil.SmtResult := .unknown none 0
      d.resultPromise.resolve result
      mgr ← mgr.recordDischargerResult d.id result
    ref.set mgr

#gen_theorems

run_cmd checkPublishedVCTheorems `InteractiveWPTransitionTheorems #[`keep_all_marked, `keep_all_marked_tr]

run_cmd do
  let mgr ← Veil.Verifier.vcManager.atomically fun ref => ref.get
  for (id, vc) in mgr.nodes.toArray do
    if vc.name == `keep_all_marked_tr then
      unless (mgr.provenWitness? id).isNone do
        throwError "expected the transition theorem to use the interactive WP proof"

end InteractiveWPTransitionTheorems

veil module DegenerateTransitionTheorems

relation marked : Bool
#gen_state
after_init { marked := true }
transition keep { True }
transition blocked { False }
invariant [trivial_inv] True
#gen_spec
#gen_theorems

run_cmd checkPublishedVCTheorems `DegenerateTransitionTheorems #[
  `keep_trivial_inv, `keep_trivial_inv_tr, `blocked_trivial_inv, `blocked_trivial_inv_tr]

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
