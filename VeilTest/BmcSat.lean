module

public import Veil

veil module BmcSat

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action set_flag {
  flag := true;
}

invariant ¬ flag

#gen_spec

/--
info: ✅ Satisfying trace found
  State 0 (via init):
    flag = false
-/
#guard_msgs in
sat trace [possible] { }

#guard_msgs(drop warning, drop info) in
sat trace {
  set_flag
  set_flag
}

/-- error: No satisfying trace exists -/
#guard_msgs in
sat trace {
  assert False
}

#guard_msgs(drop warning, drop info) in
sat trace {
  any 3 actions
}

-- A manual SAT proof supplies a concrete trace, including its action tag.
sat trace [manualSat] { set_flag } by
  refine ⟨ActionTag_IndT, inferInstance, ActionTag_IndT.set_flag, ⟨⟩, ⟨false⟩, ⟨true⟩, ?_⟩
  simp [nextSimp, smtSimp]
  rfl

-- Simulate an inconclusive primary attempt. Its placeholder is never a
-- witness for either polarity, and the grind discharger runs independently.
local macro_rules
  | `(tactic| veil_bmc) => `(tactic| exact (by sorry))

-- Let preprocessing reuse the manual witness. This produces a Lean proof
-- of existence with no SMT model to render.
attribute [local nextSimp ↓] manualSat

/-- info: Proved that a satisfying trace exists -/
#guard_msgs in
sat trace [possibleByProof] { set_flag }

#guard_msgs in
unsat trace [impossibleUnsat] { assert flag }

#gen_theorems

run_cmd do
  if (← Lean.collectAxioms ``possibleByProof).contains ``sorryAx then
    throwError "exported SAT proof contains sorry"
  let mgr ← Veil.Verifier.readVCManager
  let some vc := mgr.nodes.valuesArray.find? (·.name == `possible) | throwError "missing SAT query"
  unless vc.dischargers.size == 2 && vc.successful == some 0 do throwError "unexpected SAT dischargers"
  Lean.Elab.Command.liftTermElabM do
    let goal ← vc.toVCStatement.type
    unless goal.isAppOf ``Exists do throwError "sat trace goal is not existential"
  for name in [`impossibleUnsat, `possibleByProof] do
    let some vc := mgr.nodes.valuesArray.find? (·.name == name) | throwError "missing {name}"
    unless vc.successful == some 1 do throwError "grind discharger did not prove {name}"

end BmcSat
