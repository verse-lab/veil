module
meta import VeilTest.Regression.VerifierObserverSupport

/-!
Exercise the production registration operation and inspect Command.logSnapshotTask's
real output, with independent observer state passed through several explicit polls.
Poll ordering and late publication are deterministic; no scheduler timing is used.
-/

open Lean Elab Command Veil Veil.Verifier VeilTest.VerifierObserver
meta section

private def check (b : Bool) (message : String) : CommandElabM Unit :=
  unless b do throwError message

private def run : CommandElabM Unit := do
  let mgr ← VCManager.new vcManagerCh
  let a ← worker mgr 0 0 `A (.pure (← tree "A"))
  let b ← worker mgr 1 0 `B (.pure (← tree "B"))
  let late ← worker mgr 0 1 `late (.pure (← tree "late"))
  let (mgr, _) := mgr.addVC (← data `A) {} #[a, { late with task := none }]
  let (mgr, _) := mgr.addVC (← data `B) {} #[b]
  let old := (← get).snapshotTasks
  modify fun st => { st with snapshotTasks := #[] }
  try
    -- B goes first, then two distinct observers of A. None may consume another
    -- observer's opportunity, even when the observers have identical filters.
    let seenB ← logPendingDischargerTasks mgr (matching `B) {}
    let seenA₁ ← logPendingDischargerTasks mgr (matching `A) {}
    let seenA₂ ← logPendingDischargerTasks mgr (matching `A) {}
    check ((← get).snapshotTasks.size == 3) "independent observers lost registrations"
    let seenA₁ ← logPendingDischargerTasks mgr (matching `A) seenA₁
    let seenB ← logPendingDischargerTasks mgr (matching `B) seenB
    let seenA₂ ← logPendingDischargerTasks mgr (matching `A) seenA₂
    check ((← get).snapshotTasks.size == 3) "unchanged polls duplicated registrations"
    -- A discharger becomes started after these observers' first two polls.
    let vc := mgr.nodes[0]!
    let mgr := { mgr with nodes := mgr.nodes.insert 0 { vc with dischargers := vc.dischargers.set! 1 late } }
    let seenA₁ ← logPendingDischargerTasks mgr (matching `A) seenA₁
    let _ ← logPendingDischargerTasks mgr (matching `A) seenA₁
    let _ ← logPendingDischargerTasks mgr (matching `B) seenB
    let seenA₂ ← logPendingDischargerTasks mgr (matching `A) seenA₂
    -- An interactive registration may append a new, already-finished task.
    let interactive ← worker mgr 0 2 `interactive (.pure (← tree "interactive"))
    let mgr := mgr.addDischarger 0 { interactive with isInteractive := true }
    let _ ← logPendingDischargerTasks mgr (matching `A) seenA₁
    let _ ← logPendingDischargerTasks mgr (matching `A) seenA₂
    let _ ← logPendingDischargerTasks mgr (matching `B) seenB
    let snaps := (← get).snapshotTasks
    modify fun st => { st with snapshotTasks := old }
    check (snaps.size == 7) "late discharger missing or duplicated"
    let descriptions := snaps.map (fun snap => snap.task.get.element.desc)
    check (descriptions == #["B", "A", "A", "late", "late", "interactive", "interactive"])
      "filtering or late observation registered the wrong trees"
    for snap in snaps do
      check (snap.task.get.element.diagnostics.msgLog.toArray.size == 1)
        "registration dropped diagnostics"
      check ((snap.task.get.element.traces.tid == 41 && snap.task.get.element.traces.traces.size == 1)) "registration dropped profiling"
    liftIO <| IO.println "independent filters, repeated polls and late tasks: PASS"
  finally
    modify fun st => { st with snapshotTasks := old }

run_cmd run
