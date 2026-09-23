module

public import Veil

public section

veil module CheckInvariantsAsync

relation marked : Bool
#gen_state
after_init { marked := true }
action keep { pure () }
invariant [all_marked] marked
#gen_spec

-- Hold invariant dischargers until elaboration of #check_invariants returns.
-- A watchdog makes a blocking regression fail instead of hanging the test.
open Lean Elab Command in
run_cmd do
  let gate ← IO.Promise.new
  Veil.Verifier.withVCManager fun ref => do
    let mgr ← ref.get
    let nodes := mgr.nodes.map fun _ vc =>
      if Veil.Verifier.isDoesNotThrow vc.metadata then vc
      else { vc with dischargers := vc.dischargers.map fun d =>
        { d with mkTask := BaseIO.bindTask gate.result? fun _ => do
          let started ← d.run
          pure started.task.get! } }
    ref.set { mgr with nodes }
  discard <| IO.asTask (do
    IO.sleep 5000
    gate.resolve false)
  try
    elabCommand (← `(command| #check_invariants))
    if ← gate.isResolved then
      throwError "#check_invariants blocked command elaboration while proofs were pending"
    let env ← getEnv
    for name in #[`CheckInvariantsAsync.keep_all_marked, `CheckInvariantsAsync.keep_all_marked_tr,
        `CheckInvariantsAsync.Invariants.is_inv, `CheckInvariantsAsync.all_marked.is_inv] do
      if env.contains name then
        throwError "#check_invariants reserved an interactive theorem name: {name}"
  finally
    gate.resolve true

#gen_theorems

run_cmd do
  let env ← Lean.getEnv
  for name in #[`CheckInvariantsAsync.keep_all_marked, `CheckInvariantsAsync.keep_all_marked_tr,
      `CheckInvariantsAsync.Invariants.is_inv, `CheckInvariantsAsync.all_marked.is_inv] do
    unless env.contains name do
      throwError "#gen_theorems did not publish {name}"

end CheckInvariantsAsync
