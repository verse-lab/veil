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
