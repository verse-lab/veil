module

public import VeilTest.Regression.ImportedProofs.Spec
meta import VeilTest.Regression.ImportedProofs.Spec

veil module NodeProofs

/-- info: ✅ No violation (explored 1 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 2 } {}
/-- info: ✅ No violation (explored 1 states) -/
#guard_msgs in
#model_check compiled { node := Fin 2 } {}

end NodeProofs

veil module FlagProofs

/-- error: The specification of module FlagProofs has already been finalized. You can no longer add procedures or assertions! -/
#guard_msgs in
invariant [lateImported] False

/-- error: Declare temporal properties before `#gen_spec` in the specification of module `FlagProofs`. -/
#guard_msgs in
temporal (only := check) [lateImportedProperty] □ ⊤

-- A repeated #gen_spec keeps the specification finalized.
#gen_spec

/-- error: Declare temporal properties before `#gen_spec` in the specification of module `FlagProofs`. -/
#guard_msgs in
temporal (only := verify) [lateAfterPreparation] □ ⊤

prove_temporal_by [selfImplied]
  tintro h
  tassumption

run_cmd do
  let mod ← Veil.getCurrentModule
  unless mod.checkableTemporalProperties.map (·.name) == #[`offBefore, `selfImplied] &&
      mod.checkableInvariants.map (·.name) == #[`off] do
    throwError "unexpected properties in the importing file"

/-- info: ✅ No violation (explored 1 states) -/
#guard_msgs in
#model_check compiled {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 1 product states) -/
#guard_msgs in
#temporal_check [offBefore] compiled {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 1 product states) -/
#guard_msgs in
#temporal_check [selfImplied] interpreted {}

/--
info: ✅ Satisfying trace found
  State 0 (via init):
    flag = false
  State 1 (via keep):
    flag = false
-/
#guard_msgs in
sat trace [keepOff] { keep }
#guard_msgs in
unsat trace [cannotSetFlag] {
  keep
  assert flag
}

end FlagProofs
