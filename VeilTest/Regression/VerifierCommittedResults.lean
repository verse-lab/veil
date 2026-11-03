module

meta import Veil.Core.Tools.Verifier.Manager

/- Deterministic publication/commit interleavings. Tasks are synthetic: the
result promises are explicit gates, retained and released in `finally`. -/
open Lean Veil

meta section

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def mkDischarger (vcId dischargerId : Nat) (started : Bool := false)
    (interactive : Bool := false) : BaseIO (Discharger Unit) := do
  let task := Task.pure (default : Language.SnapshotTree)
  return {
    id := { managerId := 0, vcId, dischargerId, name := `test }
    isInteractive := interactive
    cancelTk := ← IO.CancelToken.new
    task := if started then some task else none
    startTimePromise := ← IO.Promise.new
    resultPromise := ← IO.Promise.new
    mkTask := pure task
  }

private def release (dischargers : Array (Discharger Unit)) : BaseIO Unit := do
  for d in dischargers do
    d.startTimePromise.resolve 0
    d.resultPromise.resolve (.unknown none 0)

private def mkManager (ds : Array (Discharger Unit))
    (fallback : Discharger Unit) : VCManager Unit Unit :=
  let (mgr, _) := (default : VCManager Unit Unit).addVC default {} ds
  let (mgr, _) := mgr.addAlternativeVC default 0 #[fallback]
  mgr.enableAll

private def readyIds (mgr : VCManager Unit Unit) : List (VCId × DischargerId) :=
  mgr.readyTasks.map fun (vc, d) => (vc.uid, d.id.dischargerId)

private def checkPending (mgr : VCManager Unit Unit) : IO Unit := do
  check (!mgr._doneWith.contains 0) "pending VC was finalized"
  check (!mgr.isDoneFiltered (fun _ => true)) "pending VC was reported done"
  check (mgr.dormantVCs.contains 1) "pending primary woke its alternative"

-- Publishing A's unknown result cannot make B ready before A is committed.
run_cmd do
  let a ← mkDischarger 0 0 true
  let b ← mkDischarger 0 1
  let fallback ← mkDischarger 1 0
  try
    let mgr := mkManager #[a, b] fallback
    a.resultPromise.resolve (.unknown none 0)
    check ((readyIds mgr).isEmpty) "uncommitted A made B ready"
    let mgr ← mgr.recordDischargerResult a.id (.unknown none 0)
    checkPending mgr
    check ((readyIds mgr) == [(0, 1)]) "committed unknown did not advance to B"
  finally
    release #[a, b, fallback]

-- Construct the race's second state directly: B has already started when A's
-- notification is accepted. No ready solver does not imply exhaustion.
run_cmd do
  let a ← mkDischarger 0 0 true
  let b ← mkDischarger 0 1 true
  let fallback ← mkDischarger 1 0
  try
    a.resultPromise.resolve (.unknown none 0)
    let mgr ← (mkManager #[a, b] fallback).recordDischargerResult a.id (.unknown none 0)
    checkPending mgr
    check ((readyIds mgr).isEmpty) "running B was offered for scheduling"
    b.resultPromise.resolve (.proven none none 0)
    let mgr ← mgr.recordDischargerResult b.id (.proven none none 0)
    check (mgr._doneWith[0]? == some .proven) "B's proof did not finish the VC"
    check (mgr.dormantVCs.contains 1) "B's proof woke the alternative"
  finally
    release #[a, b, fallback]

-- Even the final promise can be published before the manager accepts A.
-- Its error must be included in the aggregate only after B is committed.
run_cmd do
  let a ← mkDischarger 0 0 true
  let b ← mkDischarger 0 1 true
  let fallback ← mkDischarger 1 0
  try
    a.resultPromise.resolve (.unknown none 0)
    b.resultPromise.resolve (.error #[] 0)
    let mgr ← (mkManager #[a, b] fallback).recordDischargerResult a.id (.unknown none 0)
    checkPending mgr
    let mgr ← mgr.recordDischargerResult b.id (.error #[] 0)
    check (mgr._doneWith[0]? == some .error) "final committed error was omitted"
    check (!mgr.dormantVCs.contains 1) "exhausted primary did not wake alternative"
    check (mgr.enabledVCs.contains 1) "alternative was not enabled"
    check ((readyIds mgr) == [(1, 0)]) "woken alternative was not runnable"
  finally
    release #[a, b, fallback]

-- Both inconclusive outcomes advance; conclusive outcomes stop with unused
-- strategies, and only a failed primary activates alternatives.
run_cmd do
  for first in #[DischargerResult.unknown (ResultT := Unit) none 0, .error #[] 0] do
    for last in #[DischargerResult.proven (ResultT := Unit) none none 0, .disproven none 0] do
      let a ← mkDischarger 0 0 true
      let b ← mkDischarger 0 1
      let c ← mkDischarger 0 2
      let fallback ← mkDischarger 1 0
      try
        a.resultPromise.resolve first
        let mgr ← (mkManager #[a, b, c] fallback).recordDischargerResult a.id first
        checkPending mgr
        check ((readyIds mgr) == [(0, 1)]) "inconclusive result did not advance"
        -- Follow the server's start/write-back path before completing B.
        let b ← b.run
        let vc := {mgr.nodes[0]! with dischargers := mgr.nodes[0]!.dischargers.set! 1 b}
        let mgr := {mgr with nodes := mgr.nodes.insert 0 vc}
        check ((readyIds mgr).isEmpty) "started B was offered for scheduling again"
        b.resultPromise.resolve last
        let mgr ← mgr.recordDischargerResult b.id last
        let expected := if last.isSuccessful then VCStatus.proven else .disproven
        check (mgr._doneWith[0]? == some expected) "conclusive result did not finish"
        let expectedReady := if last.isSuccessful then [] else [(1, 0)]
        check ((readyIds mgr) == expectedReady) "wrong work after conclusive result"
        check (mgr.dormantVCs.contains 1 == last.isSuccessful) "wrong fallback activation"
      finally
        release #[a, b, c, fallback]

-- Interactive results take precedence; pending interactive work must also
-- prevent premature exhaustion, while automatic work never gets scheduled.
run_cmd do
  let auto ← mkDischarger 0 0 true
  let first ← mkDischarger 0 1 true true
  let second ← mkDischarger 0 2 true true
  let fallback ← mkDischarger 1 0
  try
    auto.resultPromise.resolve (.proven none none 0)
    first.resultPromise.resolve (.error #[] 0)
    let mgr ← (mkManager #[auto, first, second] fallback).recordDischargerResult auto.id (.proven none none 0)
    checkPending mgr
    check (mgr.nodes[0]!.successful.isNone) "automatic proof overrode interactive work"
    let mgr ← mgr.recordDischargerResult first.id (.error #[] 0)
    checkPending mgr
    check ((readyIds mgr).isEmpty) "interactive VC scheduled an automatic solver"
    second.resultPromise.resolve (.unknown none 0)
    let mgr ← mgr.recordDischargerResult second.id (.unknown none 0)
    check (mgr._doneWith[0]? == some .error) "interactive failure aggregation changed"
    check (mgr.dormantVCs.contains 1) "interactive failure woke alternative"
  finally
    release #[auto, first, second, fallback]

run_cmd do
  let auto ← mkDischarger 0 0 true
  let interactive ← mkDischarger 0 1 true true
  let fallback ← mkDischarger 1 0
  try
    interactive.resultPromise.resolve (.proven none none 0)
    let mgr ← (mkManager #[auto, interactive] fallback).recordDischargerResult interactive.id (.proven none none 0)
    check (mgr._doneWith[0]? == some .proven) "interactive proof did not finish"
    check (mgr.nodes[0]!.successful == some 1) "interactive proof was not selected"
    check ((readyIds mgr).isEmpty) "automatic work ran after interactive proof"
    check (mgr.dormantVCs.contains 1) "interactive proof woke alternative"
    auto.resultPromise.resolve (.unknown none 0)
    let mgr ← mgr.recordDischargerResult auto.id (.unknown none 0)
    check (mgr._doneWith[0]? == some .proven) "late automatic result overrode interactive proof"
  finally
    release #[auto, interactive, fallback]
