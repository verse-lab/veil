/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import ProofWidgets.Data.Html
import ProofWidgets.Util
import Veil.Core.UI.Widget.RefreshComponentUtil

/-!
## The `RefreshComponent` widget

This file defines `RefreshComponent`, which allows you to have an HTML widget that updates
incrementally as more results are computed by a Lean computation.

For this interaction, we use an `IO.Ref` that the JavaScript reads from.
It stores the HTML that should currently be on display, and a task returning the next HTML.
To determine whether the widget is up to date, each computed HTML has an associated index.
(So, the `n`-th HTML will have index `n`)

When the widget (re)loads, it first loads the current HTML from the ref, and then
repeatedly awaits further HTML result.
-/

namespace ProofWidgets
open Lean Server Widget Jsx
namespace RefreshComponent

/-- The result that is sent to the `RefreshComponent` after each query. -/
structure ResultProps where
  /-- The new HTML that will replace the current HTML. -/
  html : Html
  /-- The index of the HTML. It it is a count of how many HTMLs were created. -/
  idx : Nat
  deriving RpcEncodable, Inhabited

/-- The `RefreshState` stores the incremental result of the HTML computation. -/
structure RefreshState where
  /-- The state that the widget should currently be in. -/
  curr : ResultProps
  /-- A task that returns the next state for the widget.
  It is implemented using `IO.Promise.result?`, or `.pure none`. -/
  next : Task (Option ResultProps)

/-- A reference to a `RefreshState`. This is used to keep track of the refresh state. -/
def RefreshRef := IO.Ref RefreshState

instance : TypeName RefreshRef := unsafe .mk RefreshRef ``RefreshRef

structure RequestProps where
  state : WithRpcRef RefreshRef
  oldIdx : Nat
  deriving RpcEncodable


/-- `awaitRefresh` is called through RPC to obtain the next HTML to display. -/
@[server_rpc_method]
def awaitRefresh (props : RequestProps) : RequestM (RequestTask (Option ResultProps)) := do
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
def getCurrState (ref : WithRpcRef RefreshRef) : RequestM (RequestTask ResultProps) := do
  return .pure (← ref.val.get).curr


deriving instance TypeName for IO.CancelToken

/-- `cancelRefresh` is called through RPC by `RefreshComponent` upon cancellation.
It sets the cancel token for the task(s) on the Lean side. -/
@[server_rpc_method]
def cancelRefresh (cancelTk : WithRpcRef IO.CancelToken) : RequestM (RequestTask Unit) := do
  cancelTk.val.set
  return .pure ()


/-- The arguments passed to `RefreshComponent`. -/
structure RefreshComponentProps where
  /-- The refresh state that is queried for updating the display. -/
  state : WithRpcRef RefreshRef
  /-- The cancel token that will be set when the component is unloaded/reloaded. -/
  cancelTk : Option (WithRpcRef IO.CancelToken)
  deriving RpcEncodable

/-- Display an inital HTML, and repeatedly update the display with new HTML objects
as they appear in `state`. A dedicated thread should be spawned in order to modify `state`. -/
@[widget_module]
def RefreshComponent : Component RefreshComponentProps where
  javascript := include_str ".." / ".." / ".." / ".." / ".lake" / "build" / "js" / "RefreshComponent.js"


/-! ## API for creating `RefreshComponent`s -/

/-- The monad transformer for maintaining a `RefreshComponent`. -/
abbrev RefreshT (m : Type → Type) :=
  ReaderT (IO.Promise ResultProps) <| StateRefT' IO.RealWorld RefreshState m

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

/-- Update `RefreshState` and resolve `IO.Promise ResultProps` using the given `RefreshStep`. -/
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

/-- Update `RefreshState` and resolve `IO.Promise ResultProps` using the given `RefreshStep`.
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

/-- Store a `IO.CancelToken` for all widgets initialized by `mkGoalRefreshComponent`. -/
initialize cancelTokenMap : IO.Ref (Std.HashMap Name IO.CancelToken) ←
  IO.mkRef {}

end RefreshComponent

open RefreshComponent

/--
Create a `RefreshComponent` in the context of a `Widget.InteractiveGoal`.
This should be used when the refreshing widget depends on shift-clicked expressions in the goal.

Warning: the thread that is updating `state` has started running on the Lean server before the
widget is activated. The advantage is that there is no delay before the computation starts.
The disadvantage is that if a `RefreshComponent` is reloaded/unloaded too quickly,
it doesn't call `cancelRefresh`, and the thread will continue running unneccessarily.
To fix this, we globally store a cancel token for each such widget.
The argument `key` is used to differentiate the widgets for this purpose.
If the same widget is loaded again, we set the previous cancel token.
As a result, there can be at most one instance of that particular widget
running at a time, and any other instances will say `This component was cancelled`.
This is usually not an issue because there is no reason to have the widget duplicated.

TODO: when the infoview gets closed, `cancelRefresh` isn't run, and I don't know how to fix this.
-/
def mkGoalRefreshComponent (goal : Widget.InteractiveGoal) (initial : Html)
    (k : MetaM (RefreshStep MetaM)) (key : Name := by exact decl_name%) : BaseIO Html := do
  let cancelTk ← IO.CancelToken.new
  if let some oldTk ← cancelTokenMap.modifyGet fun map => (map[key]?, map.insert key cancelTk) then
    oldTk.set
  let promise ← IO.Promise.new
  let ref ← IO.mkRef { curr := { html := initial, idx := 0 }, next := promise.result? }
  discard <| IO.asTask (prio := .dedicated) do
    goal.ctx.val.runMetaM {} do withTheReader Core.Context ({ · with cancelTk? := cancelTk }) do
      let decl ← goal.mvarId.getDecl
      let lctx := decl.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx decl.localInstances <| (runRefreshStepM k) promise ref
  return <RefreshComponent
    state={← WithRpcRef.mk ref}
    cancelTk={← WithRpcRef.mk cancelTk}/>

/-- Create a `RefreshComponent`. To support cancellation, `m` should extend `CoreM`,
and hence have access to a cancel token. -/
def mkRefreshComponentM {m ε} [Monad m] [MonadDrop m (EIO ε)] [MonadLiftT BaseIO m]
    [MonadLiftT (ST IO.RealWorld) m] [MonadAlwaysExcept Exception m]
    (initial : Html) (k : m (RefreshStep m)) : m Html := do
  let promise ← IO.Promise.new
  let ref ← IO.mkRef { curr := { html := initial, idx := 0 }, next := promise.result? }
  discard <| EIO.asTask (prio := .dedicated) <| ← dropM <| (runRefreshStepM k) promise ref
  return <RefreshComponent
    state={← WithRpcRef.mk ref}
    cancelTk={none}/>

end ProofWidgets
