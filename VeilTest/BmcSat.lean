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

#guard_msgs in
unsat trace [impossibleUnsat] { assert flag }

run_cmd do
  let mgr ← Veil.Verifier.readVCManager
  for name in [`possible, `impossibleUnsat] do
    let some vc := mgr.nodes.valuesArray.find? (·.name == name) | throwError "missing {name}"
    unless vc.dischargers.size == 1 do throwError "unexpected trace fallback for {name}"
  let some vc := mgr.nodes.valuesArray.find? (·.name == `possible) | throwError "missing SAT query"
  Lean.Elab.Command.liftTermElabM do
    let goal ← vc.toVCStatement.type
    unless goal.isAppOf ``Exists do throwError "sat trace goal is not existential"

end BmcSat
