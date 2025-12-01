import Lean.Server.Rpc.Basic
import Lean.Elab.Command

import ProofWidgets.Component.Basic
import ProofWidgets.Component.HtmlDisplay

section
namespace ProofWidgets
open Lean Server

/-- The `State` is expected to have a `ToJson` instance that returns an object,
where the keys are field names (as strings) and the values are the field
values (as numbers, strings, arrays, or objects). -/
structure Step (State TransitionLabel : Type) where
  label : TransitionLabel
  postState : State
deriving Repr, Inhabited

structure Trace (State TransitionLabel : Type) where
  start : State
  steps : List (Step State TransitionLabel)
deriving Repr, Inhabited

instance jsonOfTrace {State TransitionLabel : Type} [ToJson State] [ToJson TransitionLabel] : ToJson (Trace State TransitionLabel) where
  toJson := fun tr =>
    let states : Array Json :=
      #[ Json.mkObj
        [ ("index", toJson 0),
          ("fields", toJson tr.start),
          ("transition", "after_init") ]] ++
      (tr.steps.toArray.mapIdx (fun i st =>
        let idx := i + 1
        Json.mkObj
        [ ("index", toJson idx),
          ("fields", toJson st.postState),
          ("transition", toJson st.label)]))
    Json.arr states

structure TraceDisplayProps where
  /-- The trace to display, as the JSON-encoded value of a `Trace` instance. -/
  trace : Json
  /-- Display orientation: "vertical" or "horizontal" -/
  layout : String := "vertical"
deriving RpcEncodable

@[widget_module]
def TraceDisplayViewer : Component TraceDisplayProps where
  javascript := include_str "." / "traceDisplay.js"

namespace DisplayTraceCommand

/-- Display a value of type `Json` (obtained from a `Trace` instance) in the infoview. -/
syntax (name := displayTraceCmd) "#displayTrace " term : command

open Lean Elab Command in
@[command_elab displayTraceCmd]
def elabDisplayTraceCmd : CommandElab := fun
  | stx@`(#displayTrace $trace) => do
    let t ← `(open ProofWidgets.Jsx in <TraceDisplayViewer trace={$trace} layout={"vertical"} />)
    let html ← ← liftTermElabM <| ProofWidgets.HtmlCommand.evalCommandMHtml <| ← ``(HtmlEval.eval $t)
    liftCoreM <| Widget.savePanelWidgetInfo
      (hash HtmlDisplayPanel.javascript)
      (return json% { html: $(← rpcEncode html) })
      stx
  | stx => throwError "Unexpected syntax {stx}."

-- macro_rules
--  | `(#displayTrace $trace:term) => `(open ProofWidgets.Jsx in #html <TraceDisplayViewer trace={$trace} layout={"vertical"} />)

end DisplayTraceCommand

end ProofWidgets
