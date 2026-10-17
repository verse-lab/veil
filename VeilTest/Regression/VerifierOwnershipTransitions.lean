module

public meta import Veil.Core.Tools.Verifier.Manager

public meta section
open Lean Elab Command Veil

private def attempt (id : DischargerIdentifier) : BaseIO (Discharger Unit) := do
  return {
    id, task := none, cancelTk := ← IO.CancelToken.new
    startTimePromise := ← IO.Promise.new, resultPromise := ← IO.Promise.new
    mkTask := pure (Task.pure default)}

private def data (name : Name) : CommandElabM (VCData Unit) := do
  return {name, params := #[], statement := ← `(term| True), metadata := ()}

private def proof : DischargerResult Unit := .proven (some (mkConst ``True.intro)) none 0

private def finish (mgr : VCManager Unit Unit) (vcId : Nat) (result : DischargerResult Unit)
    (slot := 0) : CommandElabM (VCManager Unit Unit) := do
  let some d := mgr.nodes[vcId]!.dischargers[slot]? | throwError "missing attempt"
  d.resultPromise.resolve result
  return ← mgr.recordDischargerResult d.id result

private def addInteractive (mgr : VCManager Unit Unit) (vcId : Nat)
    (result : DischargerResult Unit) : CommandElabM (VCManager Unit Unit) := do
  let slot := mgr.nodes[vcId]!.dischargers.size
  let d ← attempt {managerId := mgr._managerId, vcId, dischargerId := slot, name := `interactive}
  finish (mgr.addDischarger vcId {d with isInteractive := true}) vcId result slot

run_cmd do
  let mgr : VCManager Unit Unit ← VCManager.new (← Std.Channel.new)
  let (mgr, primary) := mgr.addVC (← data `primary) {}
  let (mgr, alt) := mgr.addAlternativeVC (← data `alternative) primary
  let (mgr, child) := mgr.addVC (← data `child) {primary}
  let mut mgr := mgr
  for id in [:3] do mgr ← mgr.mkAddDischarger id fun _ id _ => attempt id
  let some original := mgr.nodes[primary]!.dischargers[0]? | throwError "missing primary"
  let release ← IO.Promise.new
  let task := release.result!.map (fun (_ : Unit) => (default : Language.SnapshotTree))
  let running := {original with task := some task}
  mgr := {mgr with nodes := mgr.nodes.insert primary {mgr.nodes[primary]! with dischargers := #[running]}}
  mgr := mgr.enableAll
  mgr ← mgr.cancelUnneeded {}
  unless ← running.cancelTk.isSet do throwError "running attempt was not revoked"
  release.resolve ()
  let _ ← IO.wait task
  running.resultPromise.resolve (.error #[] 0)
  mgr ← mgr.reconcileFinished
  unless !mgr._doneWith.contains primary && !mgr.dependencyErrors.contains child &&
      mgr.dormantVCs.contains alt && (← mgr.readyTasks).isEmpty do
    throwError "revoked completion changed logical state or woke unowned fallback"
  let some queued := mgr.nodes[alt]!.dischargers[0]? | throwError "missing fallback"
  unless !(← queued.cancelTk.isSet) && queued.task.isNone do
    throwError "queued fallback was poisoned"
  mgr ← (mgr.enableIds (mgr.requestScope {primary})).restartCancelled
  let some retry := mgr.nodes[primary]!.dischargers[0]? | throwError "missing retry"
  unless retry.id.revision == running.id.revision + 1 do throwError "retry retained revoked identity"
  mgr ← mgr.recordDischargerResult running.id proof
  unless !mgr._doneWith.contains primary do throwError "revoked result overwrote retry"
  mgr ← finish mgr primary proof
  unless mgr.dormantVCs.contains alt && (← mgr.readyTasks).isEmpty do
    throwError "retry leaked an old fallback wake-up"

run_cmd do
  -- A proof registered after cancellation must remove the retry marker.
  let mgr : VCManager Unit Unit ← VCManager.new (← Std.Channel.new)
  let (mgr, vcId) := mgr.addVC (← data `manualAfterCancellation) {}
  let mgr ← mgr.mkAddDischarger vcId fun _ id _ => attempt id
  let some d := mgr.nodes[vcId]!.dischargers[0]? | throwError "missing attempt"
  let mgr := {mgr with nodes := mgr.nodes.insert vcId {mgr.nodes[vcId]! with dischargers := #[{d with task := some (Task.pure default)}]}}
  let mgr ← mgr.enableAll.cancelUnneeded {}
  let mgr ← addInteractive mgr vcId proof
  let mgr ← mgr.enableAll.restartCancelled
  unless mgr.isDone && mgr._doneWith[vcId]? == some .proven && !mgr.cancelledVCs.contains vcId do
    throwError "retry erased a newly registered interactive proof"

run_cmd do
  -- A failed prerequisite does not poison its child's unstarted resources.
  let mgr : VCManager Unit Unit ← VCManager.new (← Std.Channel.new)
  let (mgr, parent) := mgr.addVC (← data `parent) {}
  let (mgr, child) := mgr.addVC (← data `child) {parent}
  let mgr ← mgr.mkAddDischarger parent fun _ id _ => attempt id
  let mgr ← mgr.mkAddDischarger child fun _ id _ => attempt id
  let mgr ← finish mgr.enableAll parent (.error #[] 0)
  let mgr ← mgr.cancelUnneeded {}
  let some d := mgr.nodes[child]!.dischargers[0]? | throwError "missing child"
  unless !(← d.cancelTk.isSet) do throwError "blocked queued child was cancelled"
  let mgr ← addInteractive mgr parent proof
  let mgr ← mgr.enableAll.restartCancelled
  let [(vc, ready)] ← mgr.readyTasks | throwError "recovered child is not ready"
  unless vc.uid == child && !(← ready.cancelTk.isSet) do throwError "recovered child reused poisoned resources"

run_cmd do
  -- Being a prerequisite forces an alternative only while that demand lives.
  let mgr : VCManager Unit Unit ← VCManager.new (← Std.Channel.new)
  let (mgr, primary) := mgr.addVC (← data `primary) {}
  let (mgr, alt) := mgr.addAlternativeVC (← data `alternative) primary
  let (mgr, leaf) := mgr.addVC (← data `leaf) {alt}
  let mgr := mgr.enableIds (mgr.requestScope {leaf})
  unless !mgr.dormantVCs.contains alt do throwError "alternative prerequisite was not forced"
  let mgr ← mgr.cancelUnneeded {}
  let mgr := mgr.enableIds (mgr.requestScope {primary})
  unless mgr.dormantVCs.contains alt do throwError "released prerequisite demand left alternative awake"

run_cmd do
  -- Restart keeps earlier committed attempts and reconstructs only revoked work.
  let mgr : VCManager Unit Unit ← VCManager.new (← Std.Channel.new)
  let (mgr, vcId) := mgr.addVC (← data `sequence) {}
  let mut mgr := mgr
  for _ in [:3] do mgr ← mgr.mkAddDischarger vcId fun _ id _ => attempt id
  mgr ← finish mgr.enableAll vcId (.unknown none 0)
  let vc := mgr.nodes[vcId]!
  let some second := vc.dischargers[1]? | throwError "missing second attempt"
  let some third := vc.dischargers[2]? | throwError "missing third attempt"
  mgr := {mgr with nodes := mgr.nodes.insert vcId {vc with dischargers := vc.dischargers.set! 1 {second with task := some (Task.pure default)}}}
  mgr ← mgr.cancelUnneeded {}
  mgr ← mgr.enableAll.restartCancelled
  unless mgr._dischargerResults.contains (vcId, 0) && !(← third.cancelTk.isSet) do
    throwError "restart discarded completed work or cancelled queued work"
  let [(_, ready)] ← mgr.readyTasks | throwError "revoked sequence did not resume"
  unless ready.id.dischargerId == 1 && ready.id.revision == 1 do throwError "retry restarted the wrong attempt"

run_cmd do
  -- Reopening a failed primary must undo its fallback's old wake-up.
  let mgr : VCManager Unit Unit ← VCManager.new (← Std.Channel.new)
  let (mgr, root) := mgr.addVC (← data `root) {}
  let (mgr, primary) := mgr.addVC (← data `primary) {root}
  let (mgr, alt) := mgr.addAlternativeVC (← data `alternative) primary
  let mut mgr := mgr
  for id in [:3] do mgr ← mgr.mkAddDischarger id fun _ id _ => attempt id
  mgr ← finish mgr.enableAll root proof
  mgr ← finish mgr primary (.error #[] 0)
  mgr ← finish mgr alt proof
  unless !mgr.dormantVCs.contains alt do throwError "failed primary did not wake fallback"
  mgr ← addInteractive mgr root (.error #[] 0)
  unless mgr.dormantVCs.contains alt do throwError "invalidated primary kept its fallback awake"
  mgr ← addInteractive mgr root proof
  unless mgr.dormantVCs.contains alt && !mgr._doneWith.contains primary do
    throwError "reopened primary inherited an obsolete fallback state"

run_cmd do
  -- A dependent's explicit theorem remains valid when its prerequisite is
  -- temporarily withdrawn; it is blocked, then replayed after recovery.
  let mgr : VCManager Unit Unit ← VCManager.new (← Std.Channel.new)
  let (mgr, parent) := mgr.addVC (← data `parent) {}
  let (mgr, child) := mgr.addVC (← data `child) {parent}
  let mgr ← mgr.mkAddDischarger parent fun _ id _ => attempt id
  let mgr ← finish mgr.enableAll parent proof
  let mgr ← addInteractive mgr child proof
  let mgr ← addInteractive mgr parent (.error #[] 0)
  unless mgr.dependencyErrors.contains child do throwError "dependent theorem did not block"
  let mgr ← addInteractive mgr parent proof
  let mgr ← mgr.reconcileFinished
  unless mgr._doneWith[child]? == some .proven do
    throwError "prerequisite recovery permanently discarded a dependent theorem"
  unless mgr._totalDischarged == 4 do
    throwError "replaying a dependent theorem counted the same attempt twice"
