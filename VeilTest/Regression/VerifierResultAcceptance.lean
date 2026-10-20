module
meta import Veil.Core.Tools.Verifier.Manager

open Lean Veil
meta section

private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

private def worker (vcId index : Nat) (interactive := false)
    (generation := 7) : BaseIO (Discharger Nat) := do
  return {
    id := { managerId := generation, vcId, dischargerId := index, name := Name.mkNum `worker index }
    isInteractive := interactive
    cancelTk := ← IO.CancelToken.new
    task := none
    startTimePromise := ← IO.Promise.new
    resultPromise := ← IO.Promise.new
    mkTask := pure (.pure default) }

private def release (ds : Array (Discharger Nat)) : BaseIO Unit := do
  for d in ds do
    d.startTimePromise.resolve 0
    d.resultPromise.resolve (.unknown none 0)

private def manager (ds : Array (Discharger Nat)) : VCManager Unit Nat :=
  let (mgr, _) := ({ (default : VCManager Unit Nat) with _managerId := 7 }).addVC default {} ds
  mgr.enableAll

private def assertState (mgr : VCManager Unit Nat) (entries solved : Nat)
    (successful : Option Nat) (status : Option VCStatus) : IO Unit := do
  check (mgr._totalDischarged == entries) "distinct accepted result count changed"
  check (mgr._dischargerResults.size == entries) "accepted result map changed"
  check (mgr._totalSolved == solved) "currently proven VC count changed"
  check (mgr.nodes[0]!.successful == successful) "wrong successful witness selection"
  check (mgr._doneWith[0]? == status) "wrong VC completion/status"
  check (mgr.isDoneFiltered (fun _ => true) == status.isSome) "filtered completion disagrees with status"
  check (mgr.isDone == status.isSome) "completion disagrees with status"

-- Wrong VC, position, name and generation are rejected by both public entry
-- points, even when a forged interactive position would otherwise cancel work.
run_cmd do
  let auto ← worker 0 0
  let proof ← worker 0 1 true
  let ds := #[auto, proof]
  try
    let mgr := manager ds
    let invalid := #[{ proof.id with vcId := 99 }, { proof.id with dischargerId := 99 },
      { proof.id with name := `forged }, { proof.id with managerId := 6 }]
    for id in invalid do
      for useMark in #[false, true] do
        let next ← if useMark then mgr.markDischarger id (.proven none none 0)
          else mgr.recordDischargerResult id (.proven none none 0)
        assertState next 0 0 none none
        check (!(← auto.cancelTk.isSet)) "invalid notification canceled automatic task"
        check (next.enabledVCs.size == mgr.enabledVCs.size) "invalid notification changed admission"
    -- Even a self-consistent stored ID cannot name another generation.
    let stale ← worker 0 0 false 6
    try
      assertState (← (manager #[stale]).recordDischargerResult stale.id (.proven none none 0)) 0 0 none none
    finally release #[stale]
  finally release ds

-- An effective automatic result must retain its first accepted outcome/data,
-- including unknown and error, regardless of duplicate outcome conflicts.
run_cmd do
  for first in #[DischargerResult.unknown (some 11) 3, .error #[] 4,
      .proven (some (mkConst ``True.intro)) (some 12) 5] do
    let a ← worker 0 0
    let b ← worker 0 1
    try
      let mgr ← (manager #[a, b]).recordDischargerResult a.id first
      let success := if first.isSuccessful then some 0 else none
      let status := if first.isSuccessful then some VCStatus.proven else none
      assertState mgr 1 (if first.isSuccessful then 1 else 0) success status
      for duplicate in #[first, .unknown (some 88) 9, .error #[] 8,
          .proven (some (mkConst ``False.elim)) (some 99) 10] do
        for useMark in #[false, true] do
          let next ← if useMark then mgr.markDischarger a.id duplicate
            else mgr.recordDischargerResult a.id duplicate
          assertState next 1 (if first.isSuccessful then 1 else 0) success status
          let some stored := next._dischargerResults[(0, 0)]? | throwError "missing accepted result"
          check (stored.kindString == first.kindString && stored.time == first.time) "duplicate overwrote accepted outcome"
          match stored, first with
          | .proven w data _, .proven originalW originalData _ =>
            check (w == originalW && data == originalData) "duplicate overwrote proof/data"
          | .unknown data _, .unknown originalData _ => check (data == originalData) "duplicate overwrote data"
          | _, _ => pure ()
          let ready ← next.readyTasks
          check (ready.map (fun (_, d) => d.id.dischargerId) == if first.isSuccessful then [] else [1])
            "duplicate changed next automatic attempt"
    finally release #[a, b]

-- Automatic notifications hidden under interactive precedence are true no-ops.
run_cmd do
  let auto ← worker 0 0
  let proof ← worker 0 1 true
  try
    for result in #[DischargerResult.proven none (some 4) 0, .unknown none 0, .error #[] 0] do
      let mgr ← (manager #[auto, proof]).recordDischargerResult auto.id result
      assertState mgr 0 0 none none
      check (!(← auto.cancelTk.isSet)) "ignored automatic result set cancellation token"
      check ((← mgr.readyTasks).isEmpty) "ignored automatic result scheduled work"
    let mgr ← (manager #[auto, proof]).recordDischargerResult proof.id (.proven (some (mkConst ``True.intro)) none 1)
    assertState mgr 1 1 (some 1) (some .proven)
    check (← auto.cancelTk.isSet) "accepted interactive result did not cancel automatic work"
    let mgr ← mgr.recordDischargerResult auto.id (.error #[] 2)
    assertState mgr 1 1 (some 1) (some .proven)
  finally release #[auto, proof]

-- One proof can be edited repeatedly without inflating distinct-entry counts;
-- losing the final valid proof decrements the currently-proven VC counter.
run_cmd do
  let proof ← worker 0 0 true
  try
    let mgr ← (manager #[proof]).recordDischargerResult proof.id (.proven (some (mkConst ``True.intro)) none 1)
    assertState mgr 1 1 (some 0) (some .proven)
    let mgr ← mgr.markDischarger proof.id (.error #[] 2)
    assertState mgr 1 0 none (some .error)
    check (mgr.provenWitness? 0 |>.isNone) "failed replacement retained stale witness"
    let mgr ← mgr.recordDischargerResult proof.id (.proven (some (mkConst ``True.intro)) none 3)
    assertState mgr 1 1 (some 0) (some .proven)
  finally release #[proof]

-- An error from a different proof, or replacement of the selected proof, must
-- retain another valid witness and keep the VC solved.
run_cmd do
  let p ← worker 0 0 true
  let q ← worker 0 1 true
  try
    let mgr ← (manager #[p, q]).recordDischargerResult p.id (.proven (some (mkConst ``True.intro)) none 1)
    let mgr ← mgr.recordDischargerResult q.id (.error #[] 2)
    assertState mgr 2 1 (some 0) (some .proven)
    let mgr ← mgr.recordDischargerResult q.id (.proven (some (mkConst ``True.intro)) none 3)
    let mgr ← mgr.recordDischargerResult p.id (.error #[] 4)
    assertState mgr 2 1 (some 1) (some .proven)
    check (mgr.provenWitness? 0 |>.isSome) "remaining proof witness was lost"
    let mgr ← mgr.recordDischargerResult q.id (.error #[] 5)
    assertState mgr 2 0 none (some .error)
    let mgr ← mgr.recordDischargerResult p.id (.unknown none 6)
    assertState mgr 2 0 none (some .error)
  finally release #[p, q]

-- Projection rebases IDs over growing automatic arrays, preserves other proof
-- successes and derives counters without mutating or canceling its base.
run_cmd do
  let auto ← worker 0 0
  let extra ← worker 0 1
  let p ← worker 0 0 true
  let q ← worker 0 1 true
  let stale ← worker 0 0 true 6
  try
    let base ← (manager #[auto]).recordDischargerResult auto.id (.proven (some (mkConst ``True.intro)) none 0)
    let base := base.addDischarger 0 extra
    let success : DischargerResult Nat := .proven (some (mkConst ``True.intro)) none 1
    let view ← base.withInteractiveResults #[(p, success), (q, .error #[] 2), (stale, success)]
    assertState view 3 1 (some 2) (some .proven)
    check (view.nodes[0]!.dischargers.size == 4) "projection did not rebase or rejected wrong generation"
    check (view.provenWitness? 0 |>.isSome) "projection lost valid interactive witness"
    let errorView ← base.withInteractiveResults #[(p, .error #[] 2)]
    assertState errorView 2 0 none (some .error)
    assertState base 1 1 (some 0) (some .proven)
    check (!(← auto.cancelTk.isSet) && !(← extra.cancelTk.isSet)) "projection canceled automatic task"
  finally release #[auto, extra, p, q, stale]

-- Aggregate solved counts belong to VCs, and replacing one VC's final proof
-- must leave the other VC's proof counted.
run_cmd do
  let p ← worker 0 0 true
  let q ← worker 1 0 true
  try
    let (mgr, _) := (manager #[p]).addVC default {} #[q]
    let mgr ← mgr.recordDischargerResult p.id (.proven none none 1)
    let mgr ← mgr.recordDischargerResult q.id (.proven none none 1)
    check (mgr._totalSolved == 2 && mgr._totalDischarged == 2) "distinct proven VCs were not counted"
    let mgr ← mgr.recordDischargerResult p.id (.error #[] 2)
    check (mgr._totalSolved == 1 && mgr._totalDischarged == 2) "one replacement changed another VC's count"
    check (mgr.nodes[1]!.successful == some 0 && mgr._doneWith[1]? == some .proven) "one replacement changed another VC's proof"
    let mgr ← mgr.recordDischargerResult q.id (.error #[] 3)
    check (mgr._totalSolved == 0 && mgr._totalDischarged == 2 && mgr.isDone) "aggregate count/completion remained stale"
  finally release #[p, q]
