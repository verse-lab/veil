/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Util
import Veil.Core.UI.Widget.RefreshComponentUtil

/-!
# The `RefreshComponent` widget

This file defines `RefreshComponent`, which allows you to have an HTML widget that updates
incrementally as more results are computed by a Lean computation.

For this interaction, we use an `IO.Ref` that the JavaScript reads from.
It stores the HTML that should currently be on display, and a task returning the next HTML.
To determine whether the widget is up to date, each computed HTML has an associated version number.
(So, the `n`-th HTML will have index `n`)

When the widget (re)loads, it first loads the current HTML from the ref, and then
repeatedly awaits further HTML result.

## Known limitations

Cancellation is a bit hard to get right, and there are two limitations.

1. When using a `RefreshComponent` that reacts to shift-clicking in the infoview,
we want to cancel the computation whenever a new selection is made.
We acomplish this in `mkCancelPanelWidget` by creating a reference to a cancel token,
which we can reset every time a new selection is made.
On the other hand, we would also like to cancel the computation if that part of the file gets
reloaded. Unfortunately, the `CoreM` monad can only store up to 1 cancel token at a time.
The result is that if you close the infoview while the widget is active, and then reload
this part of the file, the widget computation keeps running without any way to stop it
(except for restarting the file, or waiting it out)
2. When using a `RefreshComponent` that comes directly from a command/tactic (no shift-clicking),
then we pass the cancel token used by elaboration to the refresh component computation.
Unfortunately there is an edge case where the cancel token gets set while the corresponding
command does not get re-elaborated. In particular, if you have three command in a row, e.g.
```
#html countToTen
#html countToTen
#html countToTen
```
Then commenting out the third command will cancel the widget of the first command.
It refreshes the second command, and doesn't affect commands before the first command - only
the first command gets badly affected.
-/

public meta section

namespace ProofWidgets
open Lean Server Widget Jsx
namespace RefreshComponent

/-- The result that is sent to the `RefreshComponent` after each query. -/
structure VersionedHtml where
  /-- The new HTML that will replace the current HTML. -/
  html : Html
  /-- The version number of the HTML. It is a count of how many HTMLs were created. -/
  idx : Nat
  deriving RpcEncodable, Nonempty

/-- The `RefreshState` stores the incremental result of the HTML computation. -/
structure RefreshState where
  /-- The state that the widget should currently be in. -/
  curr : VersionedHtml
  /-- A task that returns the next state for the widget.
  It is always implemented using `IO.Promise.result?`. -/
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

end RefreshComponent

open RefreshComponent

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


/-! ## API for creating a `RefreshComponent` -/

/-- A `RefreshToken` allows you to update the state of the corresponding `RefreshComponent`
using `RefreshToken.refresh`. -/
structure RefreshToken where
  /-- The reference that was given to the corresponding `RefreshComponent`. -/
  refreshRef : RefreshRef
  /-- The promise that will resolve the `next` field in `ref`.
  If we drop the reference to this structure, and hence to this promise,
  the `next` field will resolve to `none`. -/
  private promise : IO.Ref (IO.Promise VersionedHtml)

/-- Create a fresh `RefreshToken` with initial HTML `initial`. -/
private def RefreshToken.new (initial : Html) : BaseIO RefreshToken := do
  let promise ← IO.Promise.new
  return {
    refreshRef := ← IO.mkRef { curr := { html := initial, idx := 0 }, next := promise.result? }
    promise := ← IO.mkRef promise }

/-- Update the current HTML to be `html`.
This function makes use of `ST.Ref.take` in order to be thread safe.
That is, if multiple different threads call `RefreshToken.refresh` with the same refresh token,
a call will block other calls until it is finished. -/
def RefreshToken.refresh (token : RefreshToken) (html : Html) : BaseIO Unit := unsafe do
  let { refreshRef, promise } := token
  let idx := (← refreshRef.take).curr.idx + 1
  (← promise.get).resolve { html, idx }
  let newPromise ← IO.Promise.new
  promise.set newPromise
  refreshRef.set { curr := { html, idx }, next := newPromise.result? }

variable {m} [Monad m] [MonadDrop m (EIO Exception)] [MonadLiftT BaseIO m]

/-- Create an HTML, together with a `RefreshToken` that can be used to update this HTML. -/
def mkRefreshComponent (initial : Html := .text "") : BaseIO (Html × RefreshToken) := do
  let token ← RefreshToken.new initial
  return (<RefreshComponent state={← WithRpcRef.mk token.refreshRef}/>, token)

/-- Create a `RefreshComponent`. In order to implicitly support cancellation, `m` should extend
`CoreM`, and hence have access to a cancel token. -/
def mkRefreshComponentM (initial : Html) (k : RefreshToken → m Unit) : m Html := do
  let (html, token) ← mkRefreshComponent initial
  discard <| BaseIO.asTask (prio := .dedicated) <|
    (← dropM <| k token).catchExceptions fun ex => token.refresh =<< do
      if let .internal id _ := ex then
        if id == interruptExceptionId then
          return .text "This component was cancelled"
      return <span>
          An error occurred while refreshing this component:
          <InteractiveMessage msg={← WithRpcRef.mk ex.toMessageData}/>
        </span>
  return html

/-- Create a `RefreshComponent`. Explicitly support cancellation by creating a cancel token,
and setting the previous cancel token. This is useful when the component depends on the selections
in the goal, so that after making a new selection, the previous computation is cancelled.

Note: The cancel token is only set when a new computation is started.
  When the infoview is closed, this unfortunately doesn't set the cancel token. -/
def mkCancelRefreshComponent [MonadWithReaderOf Core.Context m]
    (cancelTkRef : IO.Ref IO.CancelToken) (initial : Html) (k : RefreshToken → m Unit) :
    m Html := do
  let cancelTk ← IO.CancelToken.new
  let oldTk ← (cancelTkRef.swap cancelTk : BaseIO _)
  oldTk.set
  mkRefreshComponentM initial fun token ↦
    withTheReader Core.Context ({· with cancelTk? := cancelTk }) <| k token

abbrev CancelTokenRef := IO.Ref IO.CancelToken

instance : TypeName CancelTokenRef := unsafe .mk CancelTokenRef ``CancelTokenRef

/-- `CancelPanelWidgetProps` are the arguments passed to a widget which supports cancellation. -/
structure CancelPanelWidgetProps extends PanelWidgetProps where
  /-- `cancelTkRef` is a reference to the cancel token of the most recent instance of the widget. -/
  cancelTkRef : WithRpcRef (IO.Ref IO.CancelToken)
  deriving RpcEncodable

/-- Return a widget that supports cancellation via `CancelPanelWidgetProps`.
The widget can be activated with for example `addPanelWidgetLocal` or  `addPanelWidgetGlobal`. -/
def mkCancelPanelWidget (component : Component CancelPanelWidgetProps) : CoreM WidgetInstance := do
  let cancelTkRef ← WithRpcRef.mk (← IO.mkRef (← IO.CancelToken.new))
  Widget.WidgetInstance.ofHash component.javascriptHash
    (return json% {cancelTkRef : $(← rpcEncode cancelTkRef)})

end ProofWidgets
