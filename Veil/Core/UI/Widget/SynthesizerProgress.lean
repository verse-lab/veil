module

public meta import Veil.Core.Tools.Synthesizer.Progress
public meta import ProofWidgets.Component.HtmlDisplay
public meta import Veil.Core.UI.Widget.RefreshComponent

public meta section

namespace Veil.Synthesizer.Progress
open Lean Elab Command ProofWidgets Jsx RefreshComponent

private def seconds (ms : Nat) : String := s!"{ms / 1000}.{(ms % 1000) / 100} s"

private def row (label value : String) : Html :=
  <tr><th style={json% {"textAlign": "left", "paddingRight": "1em"}}>{.text label}</th>
    <td>{.text value}</td></tr>

/-- This is a count of work performed, not an estimate of how far the search is from a proof. -/
def render (s : Snapshot) (now : Nat) : Html := Id.run do
  let heading := match s.status with
    | .running => s.phase
    | .finished => "Finished"
    | .stopped => "Stopped without a conclusive result"
    | .failed => "Failed"
    | .cancelled => "Cancelled"
  let elapsed := s.finishedAt.getD now - s.startedAt
  let frames := s.frameSizes.toList.zipIdx |>.map fun (n, i) => s!"F{i + 1}: {n}"
  let mut rows := #[row "Elapsed" (seconds elapsed),
    row "Search queries" s!"{s.queriesFinished} completed / {s.fuel} budget",
    row "Query time" (seconds (s.queryMs + (s.queryStartedAt.map (now - ·)).getD 0))]
  if let some started := s.queryStartedAt then
    rows := rows.push (row "Current query" s!"#{s.queriesStarted} · {seconds (now - started)}")
  if !frames.isEmpty then
    rows := rows.push (row "Clauses per frame" (String.intercalate " · " frames))
  rows := rows.push (row "Candidates / admitted clauses" s!"{s.candidates} / {s.admitted}")
  if s.obligationsTotal > 0 then
    rows := rows.push (row "Certificate obligations" s!"{s.obligationsDone} / {s.obligationsTotal}")
  return <div className="veil-synthesizer-progress">
    <strong>{.text s!"Invariant synthesis · {s.moduleName} · {heading}"}</strong>
    {if s.status == .running then <p>{.text s.activity}</p> else .text ""}
    <table>{.element "tbody" #[] rows}</table>
    {if s.lastEvent.isEmpty then .text "" else <p>{.text s.lastEvent}</p>}
    {if s.result.isEmpty then .text "" else <p>{.text s.result}</p>}
  </div>

/-- Drive one run's display until elaboration finishes or is cancelled. -/
partial def refresh (ref : Ref) (cancel? : Option IO.CancelToken)
    (token : RefreshToken) : BaseIO Unit := do
  -- Keep the same refresh state current when the cursor leaves this command. ProofWidgets
  -- cancels its UI token on unmount; stopping here would freeze the panel on remount.
  -- This task is bounded by elaboration completion/cancellation, not panel visibility.
  if let some cancel := cancel? then
    if ← cancel.isSet then
      finish (some ref) .cancelled "Elaboration was cancelled"
  let s ← ref.get
  token.update (render s (← IO.monoMsNow))
  if s.status == .running then
    IO.sleep 100
    refresh ref cancel? token

/-- Publish the panel before the synchronous search starts. Merely saving widget info would
only expose it after command elaboration finished. The same widget is retained in the final
info tree; theorem generation continues on the original command state. -/
def display (stx : Syntax) (ref : Ref) : CommandElabM Unit := do
  let (html, token) ← mkRefreshComponent (render (← ref.get) (← IO.monoMsNow))
  let wi ← liftCoreM <| Widget.WidgetInstance.ofHash (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.rpcEncode html) })
  let info := Info.ofUserWidgetInfo { wi with stx }
  pushInfoLeaf info
  let ctx ← read
  if let some snap := ctx.snap? then
    snap.old?.forM (·.val.cancelRec)
    let s ← get
    let scope := s.scopes.head!
    let tree := InfoTree.context (.commandCtx {
      env := s.env, cmdEnv? := some s.env, fileMap := ctx.fileMap, mctx := {},
      currNamespace := scope.currNamespace, openDecls := scope.openDecls,
      options := scope.opts, ngen := s.ngen }) (.node info {})
    snap.new.resolve <| .ofTyped ({ diagnostics := .empty, infoTree? := some tree }
      : Language.SnapshotLeaf)
  discard <| BaseIO.asTask (prio := .dedicated) (refresh ref ctx.cancelTk? token)

end Veil.Synthesizer.Progress
