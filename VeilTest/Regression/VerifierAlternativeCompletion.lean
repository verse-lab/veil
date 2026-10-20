module
meta import Veil.Core.Tools.Verifier.Manager

open Lean Veil
meta section

private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

private def worker (vcId index : Nat) (interactive := false)
    (started := false) : BaseIO (Discharger Unit) := do
  return {
    id := { managerId := 0, vcId, dischargerId := index, name := `worker }
    isInteractive := interactive
    cancelTk := ← IO.CancelToken.new
    task := if started then some (.pure default) else none
    startTimePromise := ← IO.Promise.new
    resultPromise := ← IO.Promise.new
    mkTask := pure (.pure default) }

private def release (ds : Array (Discharger Unit)) : BaseIO Unit := do
  for d in ds do
    d.startTimePromise.resolve 0
    d.resultPromise.resolve (.unknown none 0)

private def manager (ds : Array (Discharger Unit)) : VCManager Nat Unit :=
  let (mgr, _) := (default : VCManager Nat Unit).addVC { (default : VCData Nat) with metadata := 0 } {} ds
  mgr.enableMatching (· == 0)

private def alternative (mgr : VCManager Nat Unit) (d : Discharger Unit) : VCManager Nat Unit :=
  (mgr.addAlternativeVC { (default : VCData Nat) with metadata := 1 } 0 #[d]).1

private def readyIds (mgr : VCManager Nat Unit) : BaseIO (List Nat) := do
  return (← mgr.readyTasks).map (·.1.uid)

-- Each accepted terminal automatic failure immediately enables a late fallback,
-- even though the original command enabled only the primary's metadata.
run_cmd do
  for result in #[DischargerResult.unknown (ResultT := Unit) none 0,
      .error #[] 0, .disproven none 0] do
    let primary ← worker 0 0
    let fallback ← worker 1 0
    let gate ← IO.Promise.new
    let entered ← IO.Promise.new
    let calls ← IO.mkRef 0
    let tasks ← IO.mkRef (#[] : Array SnapshotTreeTask)
    let fallback := { fallback with mkTask := do
      let task ← BaseIO.asTask (prio := .dedicated) do
        calls.modify (· + 1)
        entered.resolve ()
        let _ ← IO.wait gate.result?
        return default
      tasks.modify (·.push task)
      return task }
    try
      let mgr ← (manager #[primary]).recordDischargerResult primary.id result
      let mgr := alternative mgr fallback
      check (!mgr.dormantVCs.contains 1 && mgr.enabledVCs.contains 1) "late failure left fallback dormant/disabled"
      check ((← readyIds mgr) == [1]) "late fallback not admitted"
      check (mgr.isDoneFiltered (· == 0) && !mgr.isDoneFiltered (· == 1) && !mgr.isDone)
        "late fallback completion/filter mismatch"
      let running ← fallback.run
      let _ ← IO.wait entered.result?
      let vc := { mgr.nodes[1]! with dischargers := #[running] }
      let mgr := { mgr with nodes := mgr.nodes.insert 1 vc }
      check ((← readyIds mgr).isEmpty) "running fallback admitted twice"
      let _ ← running.run
      check ((← calls.get) == 1) "fallback executed twice"
      gate.resolve ()
      let mgr ← mgr.recordDischargerResult fallback.id (.proven none none 0)
      check (mgr.isDone && mgr.isDoneFiltered (fun _ => true)) "completed fallback not counted"
    finally
      gate.resolve ()
      for task in ← tasks.get do let _ ← IO.wait task
      release #[primary, fallback]

-- Published promises do not constitute acceptance; accepted inconclusive work
-- with another pending/running strategy likewise cannot activate late fallbacks.
run_cmd do
  let a ← worker 0 0 false true
  let b ← worker 0 1 false true
  let fallback ← worker 1 0
  try
    a.resultPromise.resolve (.unknown none 0)
    let unpublished := alternative (manager #[a]) fallback
    check (unpublished.dormantVCs.contains 1 && !unpublished.enabledVCs.contains 1)
      "published result activated late fallback before acceptance"
    let pending ← (manager #[a, b]).recordDischargerResult a.id (.unknown none 0)
    b.resultPromise.resolve (.error #[] 0)
    let pending := alternative pending fallback
    check (pending.dormantVCs.contains 1 && !pending.enabledVCs.contains 1 && !pending.isDone)
      "partial acceptance activated late fallback"
    check ((← readyIds pending).isEmpty) "pending primary exposed fallback"
    let finished ← pending.recordDischargerResult b.id (.error #[] 0)
    check ((← readyIds finished) == [1]) "ordinary failure wakeup regressed"
  finally release #[a, b, fallback]

-- A late proof-success alternative stays dormant. Explicit failed interactive
-- proofs also suppress fallback, including a proof added after automatic failure.
run_cmd do
  for interactive in #[false, true] do
    for result in #[DischargerResult.proven (ResultT := Unit) none none 0, .error #[] 0] do
      if !interactive && !result.isSuccessful then continue
      let primary ← worker 0 0 interactive
      let fallback ← worker 1 0
      try
        let mgr ← (manager #[primary]).recordDischargerResult primary.id result
        let mgr := alternative mgr fallback
        check (mgr.dormantVCs.contains 1 && !mgr.enabledVCs.contains 1)
          "proof or explicit interactive failure activated fallback"
        check ((← readyIds mgr).isEmpty && mgr.isDone) "dormant fallback changed completion"
      finally release #[primary, fallback]
  let auto ← worker 0 0
  let proof ← worker 0 1 true
  let fallback ← worker 1 0
  try
    let mgr ← (manager #[auto]).recordDischargerResult auto.id (.unknown none 0)
    let mgr := mgr.addDischarger 0 proof
    let mgr ← mgr.recordDischargerResult proof.id (.error #[] 0)
    check ((alternative mgr fallback).dormantVCs.contains 1)
      "interactive failure after automatic failure activated fallback"
  finally release #[auto, proof, fallback]

-- A dormant alternative may have its own interactive result. Overlap must not
-- certify an unfinished primary or prevent completion once every VC is covered.
run_cmd do
  let primary ← worker 0 0
  let proof ← worker 1 0 true
  try
    let mgr := alternative (manager #[primary]) proof
    let mgr ← mgr.recordDischargerResult proof.id (.proven none none 0)
    check (mgr.dormantVCs.contains 1 && mgr._doneWith.contains 1) "missing overlap fixture"
    check (!mgr.isDone && !mgr.isDoneFiltered (fun _ => true)) "overlap certified unfinished primary"
    let mgr ← mgr.recordDischargerResult primary.id (.proven none none 0)
    check (mgr.isDone && mgr.isDoneFiltered (fun _ => true)) "overlap refused fully covered manager"
  finally release #[primary, proof]

run_cmd do
  let primary ← worker 0 0
  let proof ← worker 1 0 true
  try
    let mgr := alternative (manager #[primary]) proof
    let mgr ← mgr.recordDischargerResult proof.id (.proven none none 0)
    let mgr ← mgr.recordDischargerResult primary.id (.proven none none 0)
    check (mgr.isDone && mgr.isDoneFiltered (fun _ => true)) "overlap refused fully covered manager"
  finally release #[primary, proof]

-- Membership must cover actual node IDs, rather than just matching sizes.
run_cmd do
  let primary ← worker 0 0
  try
    let mgr := manager #[primary]
    let staleDone := { mgr with _doneWith := mgr._doneWith.insert 99 .proven }
    let staleDormant := { mgr with dormantVCs := mgr.dormantVCs.insert 99 }
    for state in #[staleDone, staleDormant] do
      check (!state.isDone && !state.isDoneFiltered (fun _ => true)) "extraneous ID certified missing node"
  finally release #[primary]
