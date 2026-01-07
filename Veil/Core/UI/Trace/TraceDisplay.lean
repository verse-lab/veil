import Lean.Server.Rpc.Basic
import Lean.Elab.Command
import Veil.Core.Tools.ModelChecker.Interface

import ProofWidgets.Component.Basic
import ProofWidgets.Component.HtmlDisplay

section
namespace ProofWidgets
open Lean Server

structure TraceDisplayProps where
  /-- The model checking result to display, as the JSON-encoded value of a
  `ModelCheckingResult` instance. -/
  result : Json
  /-- Display orientation: "vertical" or "horizontal" -/
  layout : String := "vertical"
deriving RpcEncodable

@[widget_module]
def TraceDisplayViewer : Component TraceDisplayProps where
  javascript := include_str ".." / ".." / ".." / ".." / ".lake" / "build" / "js" / "traceDisplay.js"

/-- Display a TraceDisplayViewer widget with the given result JSON.
    This can be called with a runtime Json value. -/
def displayTraceWidget (stx : Syntax) (resultJson : Json) : Elab.Command.CommandElabM Unit := do
  let props : TraceDisplayProps := { result := resultJson, layout := "vertical" }
  let html := Html.ofComponent TraceDisplayViewer props #[]
  Elab.Command.liftCoreM <| Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← rpcEncode html) })
    stx

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

namespace Veil.TraceDisplay
open Lean

private partial def fmtJson (j : Json) : String := match j with
  | .str s => s | .num n => toString n | .bool b => toString b | .null => "null"
  | .arr a => s!"[{", ".intercalate (a.map fmtJson).toList}]"
  | .obj kvs => s!"\{{", ".intercalate (kvs.toArray.map fun (k, v) => s!"{k}: {fmtJson v}").toList}}"

private def fmtFields (j : Json) (ind : String) : String := match j with
  | .obj kvs => "\n".intercalate (kvs.toArray.map fun (k, v) => s!"{ind}{k} = {fmtJson v}").toList
  | _ => fmtJson j

private def fmtAction (j : Json) : String := match j with
  | .str s => s
  | .obj kvs => match kvs.toArray.find? (·.2 != .null) with
    | some (name, .obj ps) => s!"{name}({", ".intercalate (ps.toArray.map fun (k, v) => s!"{k}={fmtJson v}").toList})"
    | some (name, _) => name | none => toString j
  | _ => toString j

private def fmtState (s : Json) (ind : String) : String :=
  let trans := match s.getObjValD "transition" with | .str "after_init" => "init" | t => fmtAction t
  s!"{ind}State {fmtJson (s.getObjValD "index")} (via {trans}):\n{fmtFields (s.getObjValD "fields") (ind ++ "  ")}"

def formatTrace (j : Json) (ind : String := "  ") : String := Id.run do
  let mut r := ""
  for (k, v) in #[("Instantiation", j.getObjValD "instantiation"), ("Theory", j.getObjValD "theory")] do
    if let .obj kvs := v then unless kvs.isEmpty do r := r ++ s!"{ind}{k}:\n{fmtFields v (ind ++ "  ")}\n"
  match j.getObjValD "states" with
  | .arr states => r ++ (states.toList.map (fmtState · ind) |> "\n".intercalate)
  | _ => r ++ s!"{ind}(no states)"

def formatModelCheckingResult (j : Json) : MessageData :=
  match fmtJson (j.getObjValD "result") with
  | "found_violation" =>
    let v := j.getObjValD "violation"
    let violates := match v.getObjValD "violates" with
      | .arr arr => if arr.isEmpty then "" else s!" (violates: {", ".intercalate (arr.map fmtJson).toList})"
      | _ => ""
    m!"❌ Violation: {fmtJson (v.getObjValD "kind")}{violates}\n{formatTrace (j.getObjValD "trace")}"
  | "no_violation_found" =>
    let trace := j.getObjValD "trace"
    if trace != .null then m!"✅ Satisfying trace found\n{formatTrace trace}"
    else m!"✅ No violation (explored {fmtJson (j.getObjValD "explored_states")} states)"
  | "cancelled" => m!"⚠️ Cancelled"
  | r => if j.getObjValD "error" != .null then m!"💥 Error: {fmtJson (j.getObjValD "error")}" else m!"Unknown: {r}"

end Veil.TraceDisplay
