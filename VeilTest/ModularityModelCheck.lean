module

public import Examples.Modularity.Bridge
public import VeilTest.ModuleInstances
public import VeilTest.ModuleInstanceHelper

/-! Execute the composed programs, including internal procedures and checked
postconditions. Proof views must not replace concrete dispatch with summaries. -/

private meta def assertExhaustiveModelCheck (expectedStates : Nat) :
    Lean.Elab.Command.CommandElabM Unit := do
  let next ← Veil.ModelChecker.Concrete.nextInstanceId.get
  unless next > 0 do throwError "model checking did not start"
  let some refs ← Veil.ModelChecker.Concrete.getProgressRefs (next - 1)
    | throwError "missing model checking progress"
  let mut result ← refs.resultRef.get
  -- Interpreted checks run in snapshot tasks. Wait for their actual verdict,
  -- rather than accepting successful elaboration of the command alone.
  for _ in [:1000] do
    if result.isSome then break
    IO.sleep 10
    result ← refs.resultRef.get
  let some verdict := result | throwError "model checking did not finish"
  unless verdict.getObjValD "result" == .str "no_violation_found" &&
      (verdict.getObjValD "termination_reason").getObjValD "kind" ==
        .str "explored_all_reachable_states" &&
      verdict.getObjValD "explored_states" == Lean.toJson expectedStates do
    throwError "expected exhaustive exploration of {expectedStates} states, got {verdict}"

veil module FiniteBridgeInstances

type tx

isolate source : Source (tx := tx)
isolate adapter : Adapter (tx := tx) (source := source) with source
isolate destination : Destination (tx := tx) (adapter := adapter) with source, adapter

safety [backed] ∀ t : tx, destination.minted t → source.finalized t

set_option veil.deferVCGeneration true
#gen_spec
#guard_msgs(error, drop info, drop warning) in
#model_check interpreted { tx := Fin 2 }
run_cmd assertExhaustiveModelCheck 16

end FiniteBridgeInstances

veil module FiniteCounterInstances

isolate left : BoundedCounter (limit := 2)
isolate right : BoundedCounter (limit := 3)

safety [bounds] left.value ≤ 2 ∧ right.value ≤ 3
termination [done] left.value = 2 ∧ right.value = 3

set_option veil.deferVCGeneration true
#gen_spec
#guard_msgs(error, drop info, drop warning) in
#model_check interpreted {}
run_cmd assertExhaustiveModelCheck 12

end FiniteCounterInstances

veil module FiniteSharedProvider

type item

isolate source : InstanceSource (item := item) (capacity := 2)
isolate left : InstanceConsumer (item := item) (capacity := 2) (source := source) with source
isolate right : InstanceConsumer (item := item) (capacity := 2) (source := source) with source

safety [backed] ∀ i : item, (left.seen i ∨ right.seen i) → source.ready i

set_option veil.deferVCGeneration true
#gen_spec
#guard_msgs(error, drop info, drop warning) in
#model_check interpreted { item := Fin 2 }
run_cmd assertExhaustiveModelCheck 25

end FiniteSharedProvider
