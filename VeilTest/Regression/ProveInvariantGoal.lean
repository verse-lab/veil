module

public import Veil

veil module ProveInvariantGoal

type node
relation r : node → Bool

after_init { r N := false }
action keep (n : node) { require r n }
action «by» { pure () }
invariant [excluded] r N ∨ ¬ r N
invariant [«true»] r N ∨ ¬ r N

#gen_spec

-- Check the user-facing text, including all the hidden module binders.
open Lean in
run_cmd do
  let mgr ← Veil.Verifier.vcManager.atomically fun ref => ref.get
  for (name, selector) in [(`keep_excluded, "keep excluded using wp"),
      (`keep_excluded_tr, "keep excluded using tr"),
      (`keep_doesNotThrow, "keep doesNotThrow using wp"),
      (`initializer_excluded, "initializer excluded using wp"),
      (`by_true, "«by» true using wp")] do
    let some vc := mgr.nodes.valuesArray.find? (·.name == name)
      | throwError "missing {name} VC"
    let text ← Elab.Command.liftCoreM <| Veil.mkTheoremText { vc with successful := none }
    unless text == s!"prove_veil_invariant_goal {selector} by\n  sorry" do
      throwError "expected a `prove_veil_invariant_goal` interactive proof stub, got:\n{text}"

prove_veil_invariant_goal keep excluded using wp by
  done

prove_veil_invariant_goal keep excluded using tr by
  done

prove_veil_invariant_goal keep doesNotThrow using wp by
  done

prove_veil_invariant_goal initializer excluded using wp by
  done

prove_veil_invariant_goal initializer excluded using tr by
  done

prove_veil_invariant_goal «by» «true» using wp by
  done

-- Proofs done by `prove_veil_invariant_goal` must be registered as successful interactive dischargers,
-- with expanded theorem types and without introducing statement assumptions.
open Lean in
run_cmd do
  let mgr ← Veil.Verifier.vcManager.atomically fun ref => ref.get
  for name in [`keep_excluded, `keep_excluded_tr, `keep_doesNotThrow,
      `initializer_excluded, `initializer_excluded_tr, `by_true] do
    let some vc := mgr.nodes.valuesArray.find? (·.name == name)
      | throwError "missing VC {name}"
    let some discharger := vc.dischargers.find? (·.isInteractive)
      | throwError "missing interactive discharger for {name}"
    let some result := mgr._dischargerResults[(vc.uid, discharger.id.dischargerId)]?
      | throwError "missing interactive result for {name}"
    unless result.isSuccessful do
      throwError "`prove_veil_invariant_goal` did not discharge {name}"
    let info ← getConstInfo (`ProveInvariantGoal ++ name)
    unless info.type.isForall do
      throwError "`prove_veil_invariant_goal` lost its quantified parameters"
    let axioms ← collectAxioms (`ProveInvariantGoal ++ name)
    if axioms.contains ``sorryAx then
      throwError "`prove_veil_invariant_goal` contains sorry"

-- Existing theorem generation still accepts an already registered proof.
#gen_theorems

end ProveInvariantGoal
