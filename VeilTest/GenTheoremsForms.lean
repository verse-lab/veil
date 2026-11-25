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

-- The existing direct theorem has a universe parameter that disappears when
-- its statement is reduced. The companion must use an instantiated constant.
public def wrapProp.{u} (_ : Type (u+1)) (p : Prop) : Prop := p

veil module PolymorphicSource
individual flag : Bool
after_init { flag := false }
action keep { flag := false }
transition reset { flag' = false }
invariant [off] flag = false
#gen_spec
#check_action keep
#check_action reset

open Lean Elab Command in
run_cmd do
  let mgr ← Veil.Verifier.readVCManager
  for (name, tactic) in [(`keep_off, ← `(tactic| veil_solve_wp)), (`reset_off_tr, ← `(tactic| veil_solve_tr))] do
    let some vc := mgr.nodes.valuesArray.find? (·.name == name) | throwError "missing {name}"
    elabCommand (← `(command| theorem $(mkIdent name).{u} $(vc.params)* :
      wrapProp (Type u) $(vc.statement) := by unfold wrapProp; $tactic:tactic))

end PolymorphicSource

run_cmd checkForms `PolymorphicSource #[`keep_off, `keep_off_tr, `reset_off, `reset_off_tr]

-- Specialization can also require a particular nonzero level. This small VC
-- has an identity conversion, so the kernel checks the exact reused source.
namespace ConstrainedSource

set_option warn.sorry false in
public theorem source.{u} : ∀ _ : Type u, True := by sorry

set_option warn.sorry false in
set_option linter.checkUnivs false in
public theorem multi.{u,v} : ∀ _ : Type (max u v), True := by sorry

open Lean Elab Command Veil Verifier in
private meta def publishSpecialization : CommandElabM Unit := do
  runManager
  let statement ← `(∀ _ : Type 2, True)
  let level := Level.succ (.succ .zero)
  -- Infer the nonzero universe for `source`. For `multi`, the witness itself
  -- supplies an exact solution to the underdetermined max-universe constraint.
  let proofs := #[(`source, `companion, mkConst ``multi [.zero, level]),
                  (`multi, `multiCompanion, mkConst ``multi [level, .zero])]
  for (name, companion, witness) in proofs do
    let variant : VCTheoremVariant := {
      name := companion, params := #[], statement, ofProof := fun proof _ => pure proof }
    withVCManager fun ref => do
      let (mgr, id) := (← ref.get).addVC {
        name, params := #[], statement, metadata := default, variant? := some variant } {}
      ref.set { mgr with
        nodes := mgr.nodes.modify id ({ · with successful := some 0 })
        _dischargerResults := mgr._dischargerResults.insert (id, 0) (.proven (some witness) none 0) }
  addProvenTheoremsInDependencyOrder (fun _ => true)

/--
warning: Published VC theorems using `sorryAx`
  ConstrainedSource.companion
  ConstrainedSource.multiCompanion
-/
#guard_msgs in
run_cmd publishSpecialization

example : ∀ _ : Type 2, True := companion
example : ∀ _ : Type 2, True := multiCompanion

end ConstrainedSource
