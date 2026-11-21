module

public import Veil

-- Exercise the actual failure suggestion, without relying on solver timeouts.
veil module ProveInvariantGoalSuggestion
individual x : Nat
after_init { x := 0 }
action step { require x < 10; x := x + 1 }
invariant [bounded] x = 1

#gen_spec

-- Exercise the insertion UI with a controlled result for every style of the invariant.
run_cmd do
  Veil.Verifier.withVCManager fun ref => do
    let mut mgr ← ref.get
    for vc in mgr.nodes.valuesArray do
      if vc.metadata.propertyName? == some `bounded then
        for d in vc.dischargers do
          mgr ← mgr.recordDischargerResult d.id (.unknown none 0)
    ref.set mgr

-- Ignore the expected solver errors and check the complete insertion suggestion.
/--
info: Insert theorem stubs for undischarged verification conditions:

  [apply] prove_veil_invariant_goal initializer bounded using wp by
    sorry
  ⏎
  prove_veil_invariant_goal step bounded using wp by
    sorry
-/
#guard_msgs (drop error, all, whitespace := exact) in
#check_invariants

end ProveInvariantGoalSuggestion
