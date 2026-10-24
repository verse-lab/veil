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

private def clauseList (clauses : Array String) : Html :=
  if clauses.isEmpty then <p>{.text "No strengthening clauses."}</p>
  else .element "ol" #[("style", json% {"paddingLeft": "1.5em"})] <|
    clauses.map fun clause =>
      <li style={json% {"marginBottom": "0.5em"}}>
        <code style={json% {"whiteSpace": "pre-wrap", "overflowWrap": "anywhere"}}>
          {.text clause}
        </code>
      </li>

private def searchDetails (s : Snapshot) : Html :=
  -- Do not control `open`: React retains the user's expanded state across refreshes.
  <details key="search-details" style={json% {"marginTop": "0.75em"}}>
    <summary style={json% {"cursor": "pointer"}}>{.text "Frames and recent activity"}</summary>
    <div style={json% {"maxHeight": "32em", "overflowY": "auto", "paddingRight": "0.5em"}}>
      <p>{.text "F0 represents the initial states. Every frame below also includes the checked property; the lists show its strengthening clauses."}</p>
      {if s.frameClauses.isEmpty then <p>{.text "No frames opened yet."}</p>
       else .element "div" #[] <| s.frameClauses.mapIdx fun i clauses =>
         <div key={s!"frame-{i + 1}"} style={json% {"marginBottom": "1em"}}>
           <strong>{.text s!"F{i + 1} · {clauses.size} clause(s)"}</strong>
           {clauseList clauses}
         </div>}
      <strong>{.text "Recent activity"}</strong>
      <p>{.text "Latest first, up to 50 events."}</p>
      {if s.recentEvents.isEmpty then <p>{.text "No search events yet."}</p>
       else .element "ul" #[("style", json% {"paddingLeft": "1.5em"})] <|
         s.recentEvents.reverse.map fun event =>
           <li style={json% {"marginBottom": "0.5em", "overflowWrap": "anywhere"}}>
             {.text event}
           </li>}
    </div>
  </details>

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
    {searchDetails s}
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

/-- The launching command returns immediately, so ordinary widget information is sufficient.
The refresh task follows the computation's cancellation token, independently of panel visibility. -/
def display (stx : Syntax) (ref : Ref) (cancel : IO.CancelToken) : CommandElabM Unit := do
  let (html, token) ← mkRefreshComponent (render (← ref.get) (← IO.monoMsNow))
  let wi ← liftCoreM <| Widget.WidgetInstance.ofHash (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.rpcEncode html) })
  let info := Info.ofUserWidgetInfo { wi with stx }
  pushInfoLeaf info
  discard <| BaseIO.asTask (prio := .dedicated) (refresh ref (some cancel) token)

end Veil.Synthesizer.Progress
