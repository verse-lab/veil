/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import ProofWidgets.Data.Html
import ProofWidgets.Util
import ProofWidgets.Component.Panel.Basic
import Veil.Core.UI.Widget.RefreshComponentUtil

/-!
## The `RefreshComponent` widget

This file defines `RefreshComponent`, which allows you to have an HTML widget that updates
incrementally as more results are computed by a Lean computation.

For this interaction, we use an `IO.Ref` that the JavaScript reads from.
It stores the HTML that should currently be on display, and a task returning the next HTML.
To determine whether the widget is up to date, each computed HTML has an associated version number.
(So, the `n`-th HTML will have index `n`)

When the widget (re)loads, it first loads the current HTML from the ref, and then
repeatedly awaits further HTML result.
-/


namespace ProofWidgets
open Lean Server Widget Jsx
namespace RefreshComponent

/-- The result that is sent to the `RefreshComponent` after each query. -/
structure VersionedHtml where
  /-- The new HTML that will replace the current HTML. -/
  html : Html
  /-- The version number of the HTML. It is a count of how many HTMLs were created. -/
  idx : Nat
  deriving RpcEncodable, Inhabited

/-- The `RefreshState` stores the incremental result of the HTML computation. -/
structure RefreshState where
  /-- The state that the widget should currently be in. -/
  curr : VersionedHtml
  /-- A task that returns the next state for the widget.
  It is implemented using `IO.Promise.result?`, or `.pure none`. -/
  next : Task (Option VersionedHtml)

/-- A reference to a `RefreshState`. This is used to keep track of the refresh state. -/
abbrev RefreshRef := IO.Ref RefreshState

instance : TypeName RefreshRef := unsafe .mk RefreshRef ``RefreshRef

/-- The data used to call `awaitRefresh`, for updating the HTML display. -/
structure AwaitRefreshParams where
  /-- The reference to the `RefreshState`. -/
  state : WithRpcRef RefreshRef
  /-- The index of the HTML that is currently on display. -/
  oldIdx : Nat
  deriving RpcEncodable


/-- `awaitRefresh` is called through RPC to obtain the next HTML to display. -/
@[server_rpc_method]
def awaitRefresh (props : AwaitRefreshParams) : RequestM (RequestTask (Option VersionedHtml)) := do
  let { curr, next } ← props.state.val.get
  -- If `props.oldIdx < curr.idx`, that means that the state has updated in the meantime.
  -- So, returning `curr` will give a refresh.
  -- If `props.oldIdx = curr.idx`, then we need to await `next` to get a refresh
  if props.oldIdx = curr.idx then
    return .mapCheap .ok ⟨next⟩
  else
    return .pure curr

/--
`getCurrState` is called through RPC whenever the widget reloads.
This can be because the infoview was closed and reopened,
or because a different expression was selected in the goal.
-/
@[server_rpc_method]
def getCurrState (ref : WithRpcRef RefreshRef) : RequestM (RequestTask VersionedHtml) := do
  return .pure (← ref.val.get).curr

/-- The argument passed to `RefreshComponent`. -/
structure RefreshComponentProps where
  /-- The refresh state that is queried for updating the display. -/
  state : WithRpcRef RefreshRef
  deriving RpcEncodable

/-- Display an inital HTML, and repeatedly update the display with new HTML objects
as they appear in `state`. A dedicated thread should be spawned in order to modify `state`. -/
@[widget_module]
def RefreshComponent : Component RefreshComponentProps where
  javascript := include_str ".." / ".." / ".." / ".." / ".lake" / "build" / "js" / "RefreshComponent.js"


/-! ## API for creating `RefreshComponent`s -/

/-- The monad transformer for maintaining a `RefreshComponent`. -/
abbrev RefreshT (m : Type → Type) :=
  ReaderT (IO.Promise VersionedHtml) <| StateRefT' IO.RealWorld RefreshState m

variable {m : Type → Type} [Monad m] [MonadLiftT BaseIO m]
  [MonadLiftT (ST IO.RealWorld) m]

/-- `RefreshStep` represents an update to the refresh state. -/
inductive RefreshStep (m : Type → Type) where
  /-- Leaves the current HTML in place and stops the refreshing. -/
  | none
  /-- Sets the current HTML to `html` and stops the refreshing. -/
  | last (html : Html)
  /-- Sets the current HTML to `html` and continues refreshing with `cont`. -/
  | cont' (html : Html) (cont : RefreshT m Unit)
  deriving Inhabited

/-- Update `RefreshState` and resolve `IO.Promise VersionedHtml` using the given `RefreshStep`. -/
def runRefreshStep (k : RefreshStep m) : RefreshT m Unit := do
  let idx := (← get).curr.idx + 1
  match k with
  | .none =>
    modify fun { curr, .. } => { curr, next := .pure none }
    -- we drop the reference to the promise, so the corresponding task will return `none`.
  | .last html =>
    MonadState.set { curr := { html, idx }, next := .pure none }
    (← read).resolve { html, idx }
  | .cont' html cont =>
    let newPromise ← IO.Promise.new
    MonadState.set { curr := { html, idx }, next := newPromise.result? }
    (← read).resolve { html, idx }
    withReader (fun _ => newPromise) cont

/-- Update `RefreshState` and resolve `IO.Promise VersionedHtml` using the given `RefreshStep`.
Also catch all exceptions that `k` might throw. -/
def runRefreshStepM [i : MonadAlwaysExcept Exception m] (k : m (RefreshStep m)) : RefreshT m Unit := do
  have := i.except
  runRefreshStep <| ←
    try k
    catch e =>
      if let .internal id _ := e then
        if id == interruptExceptionId then
          return .last <| .text "This component was cancelled"
      return .last
        <span>
        Error refreshing this component: <InteractiveMessage msg={← WithRpcRef.mk e.toMessageData}/>
        </span>

@[inherit_doc RefreshStep.cont']
def RefreshStep.cont [MonadAlwaysExcept Exception m]
    (html : Html) (cont : m (RefreshStep m)) : RefreshStep m :=
  .cont' html (runRefreshStepM cont)

end RefreshComponent

open RefreshComponent

variable {m ε} [Monad m] [MonadDrop m (EIO ε)] [MonadLiftT BaseIO m]

/-- Create a `RefreshComponent`. In order to implicitly support cancellation, `m` should extend
`CoreM`, and hence have access to a cancel token. -/
def mkRefreshComponent (initial : Html) (k : RefreshT m Unit) : m Html := do
  let promise ← IO.Promise.new
  let ref ← IO.mkRef { curr := { html := initial, idx := 0 }, next := promise.result? }
  discard <| EIO.asTask (prio := .dedicated) <| ← dropM <| k promise ref
  return <RefreshComponent state={← WithRpcRef.mk ref}/>

/-- Create a `RefreshComponent`. Explicitly support cancellation by creating a cancel token,
and setting the previous cancel token. This is useful when the component depends on the selections
in the goal, so that after making a new selection, the previous computation is cancelled.

Note: The cancel token is only set when a new computation is started.
  When the infoview is closed, this unfortunately doesn't set the cancel token. -/
def mkCancelRefreshComponent [MonadWithReaderOf Core.Context m]
    (cancelTkRef : IO.Ref IO.CancelToken) (initial : Html) (k : RefreshT m Unit) : m Html := do
  let cancelTk ← IO.CancelToken.new
  let oldTk ← (cancelTkRef.swap cancelTk : BaseIO _)
  oldTk.set
  mkRefreshComponent initial do
    withTheReader Core.Context ({· with cancelTk? := cancelTk }) k

abbrev CancelTokenRef := IO.Ref IO.CancelToken

instance : TypeName CancelTokenRef := unsafe .mk CancelTokenRef ``CancelTokenRef

/-- `CancelPanelWidgetProps` are the arguments passed to a widget which supports cancellation. -/
structure CancelPanelWidgetProps extends PanelWidgetProps where
  /-- `cancelTkRef` is a reference to the cancel token of the most recent instance of the widget. -/
  cancelTkRef : WithRpcRef (IO.Ref IO.CancelToken)
  deriving RpcEncodable

/-- Locally display a widget that supports cancellation via `CancelPanelWidgetProps`. -/
def showCancelPanelWidget (component : Component CancelPanelWidgetProps) : CoreM Unit := do
  let cancelTkRef ← WithRpcRef.mk (← IO.mkRef (← IO.CancelToken.new))
  let wi ← Widget.WidgetInstance.ofHash component.javascriptHash
    (return json% {cancelTkRef : $(← rpcEncode cancelTkRef)})
  addPanelWidgetLocal wi

end ProofWidgets
