module

public import Veil

veil module CommandOwnedVC

individual x : Nat
after_init { x := 0 }
action step { x := 0 }
invariant [zero] x = 0
#gen_spec

sat trace [firstWitness] { } by
  refine ⟨ActionTag_IndT, inferInstance, ⟨⟩, ⟨0⟩, ?_⟩
  simp [nextSimp, smtSimp]
  rfl
sat trace [secondWitness] { } by exact firstWitness

-- A controlled inconclusive primary attempt lets each checkpoint select a
-- different explicit proof through the same fallback tactic.
local macro_rules
  | `(tactic| veil_bmc) => `(tactic| exact (by sorry))

open Lean Elab Command Veil Veil.Verifier in
#guard_msgs (drop info) in
run_cmd do
  let query ← ofExcept (Parser.runParserCategory (← getEnv) `command "sat trace [replayed] { }")
  let isReplay := fun m : VCMetadata => m.isTrace && m.propertyName? == some `replayed
  let owner ← getVCManagerOwner
  let physical := owner.manager.atomically (m := BaseIO) fun ref => ref.get
  let saved ← get

  elabCommand (← `(local macro_rules | `(tactic| veil_bmc using grind) => `(tactic| exact firstWitness)))
  elabCommand query
  let _ ← waitFilteredSync isReplay
  let oldView ← captureVCManager
  let some oldId := (← oldView).findVCByFilter isReplay | throwError "missing original trace"
  let some (firstVC, first) := (← oldView).provenWitness? oldId | throwError "missing original proof"
  unless first.getUsedConstants.contains ``firstWitness do throwError "unexpected original witness"
  let obsoleteTasks := (← get).snapshotTasks.extract saved.snapshotTasks.size

  -- Restore the same specification, retaining the first trace's snapshots so
  -- both registrations coexist while the second version is being checked.
  set saved
  elabCommand (← `(local macro_rules | `(tactic| veil_bmc using grind) => `(tactic| exact secondWitness)))
  elabCommand query
  elabCommand (← `(#gen_theorems))
  let declName := (← getCurrNamespace) ++ `replayed
  let some (.thmInfo thm) := (← getEnv).find? declName | throwError "missing exported trace theorem"
  unless thm.value.getUsedConstants.contains ``secondWitness do throwError "exported obsolete witness"

  let current ← readVCManager
  let some newId := current.findVCByFilter isReplay | throwError "missing replayed trace"
  if newId == oldId || current.nodes.contains oldId then throwError "replay reused an obsolete trace"
  let previous ← oldView
  unless previous.nodes.contains oldId && !previous.nodes.contains newId do
    throwError "replay changed the captured checkpoint"
  unless (← physical).nodes.contains oldId do throwError "old trace retired with its snapshot still live"

  -- Name-based interactive registration must also resolve the current trace.
  elabCommand (← `(attribute [veil] $(mkIdent declName):ident))
  unless (← readVCManager).nodes[newId]?.any (·.hasInteractiveDischarger) do
    throwError "interactive proof attached to the wrong registration"

  obsoleteTasks.forM (·.cancelRec)
  let deadline := (← IO.monoMsNow) + 10000
  while (← physical).nodes.contains oldId do
    if (← IO.monoMsNow) > deadline then throwError "discarded trace still registered"
    IO.sleep 1
  for d in firstVC.dischargers do
    unless ← d.cancelTk.isSet do throwError "discarded discharger still active"
  let mgr ← physical
  if mgr._dischargerResults.toArray.any (fun (key, _) => key.1 == oldId) then
    throwError "discarded trace still has results"
  unless (mgr.provenWitness? newId).isSome do throwError "retiring the old trace lost the current proof"

end CommandOwnedVC
