import Lean.Server.Rpc.Basic
import Lean.Elab.Command
import Veil.Core.Tools.ModelChecker.Interface

import ProofWidgets.Component.Basic
import ProofWidgets.Component.HtmlDisplay

namespace Veil.TraceDisplay
open Lean

/-- Which command produced the result being rendered.

Each producer emits a different JSON shape, so each gets its own renderer rather
than one renderer guessing from whichever keys happen to be present. -/
inductive ResultKind where
  /-- `#model_check`, i.e. a `ModelCheckingResult`. -/
  | modelCheck
  /-- `#simulate`, i.e. `SimulateResult.toDisplayJson`. -/
  | simulate
  /-- `sat trace` / `unsat trace`, i.e. a trace extracted from a VC. -/
  | symbolicTrace
deriving Inhabited, BEq, ToJson, FromJson

end Veil.TraceDisplay

section
namespace ProofWidgets
open Lean Server

structure TraceDisplayProps where
  /-- The model checking result to display, as the JSON-encoded value of a
  `ModelCheckingResult` instance. -/
  result : Json
  /-- Display orientation: "vertical" or "horizontal" -/
  layout : String := "vertical"
  /-- Optional raw HTML representation of the SMT model, for displaying the unprocessed model. -/
  rawHtml : Option Html := none
  /-- Which command produced `result`. The widget picks its renderer from this
  rather than from which keys happen to be present. -/
  kind : Veil.TraceDisplay.ResultKind := .modelCheck
deriving RpcEncodable

@[widget_module]
def TraceDisplayViewer : Component TraceDisplayProps where
  javascript := include_str ".." / ".." / ".." / ".." / ".lake" / "build" / "js" / "traceDisplay.js"

/-- Display a TraceDisplayViewer widget with the given result JSON.
    This can be called with a runtime Json value. -/
def displayTraceWidget (stx : Syntax) (kind : Veil.TraceDisplay.ResultKind)
    (resultJson : Json) : Elab.Command.CommandElabM Unit := do
  let props : TraceDisplayProps :=
    { result := resultJson, layout := "vertical", kind }
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

private def fmtSeedSuffix (j : Json) : String :=
  let seed := j.getObjValD "seed"
  if seed == .null then "" else s!"\nSeed: {fmtJson seed}"

private def isNoInitialStatesTermination (j : Json) : Bool :=
  match j.getObjValD "termination_reason" with
  | .obj reason => fmtJson ((Json.obj reason).getObjValD "kind") == "no_initial_states"
  | _ => false

private def fmtViolation (j : Json) (suffix : String := "") : MessageData :=
  let v := j.getObjValD "violation"
  let violates := match v.getObjValD "violates" with
    | .arr arr => if arr.isEmpty then "" else s!" (violates: {", ".intercalate (arr.map fmtJson).toList})"
    | _ => ""
  let trace := j.getObjValD "trace"
  let traceMsg := if trace == .null then "" else s!"\n{formatTrace trace}"
  m!"❌ Violation: {fmtJson (v.getObjValD "kind")}{violates}{traceMsg}{suffix}"

/-- Fallback for an unrecognised `result`, and for error payloads. Shared by all
renderers, since an error is not specific to any one command. -/
private def fmtUnexpected (result : String) (j : Json) : MessageData :=
  if j.getObjValD "error" != .null then m!"💥 Error: {fmtJson (j.getObjValD "error")}"
  else m!"Unknown: {result}"

private def formatModelCheckResult (j : Json) : MessageData :=
  match fmtJson (j.getObjValD "result") with
  | "found_violation" => fmtViolation j
  | "no_violation_found" =>
      m!"✅ No violation (explored {fmtJson (j.getObjValD "explored_states")} states)"
  | "cancelled" => m!"⚠️ Cancelled"
  | r => fmtUnexpected r j

/-- Render the non-empty buckets of a `#simulate` depth histogram, e.g.
`Trace depths: 0x1, 1x3, 4x1`. -/
private def fmtDepthHistogram (j : Json) : String :=
  let h := j.getObjValD "depth_histogram"
  let width := max 1 ((h.getObjValAs? Nat "bucket_width").toOption.getD 1)
  match h.getObjValD "counts" with
  | .arr counts =>
    let entries := (List.finRange counts.size).filterMap fun i =>
      match (Lean.fromJson? (α := Nat) counts[i]).toOption with
      | some n =>
        if n == 0 then none
        else
          let lo := i.val * width
          let label := if width == 1 then s!"{lo}" else s!"{lo}-{lo + width - 1}"
          some s!"{label}x{n}"
      | none => none
    -- A "distribution" over a single trace says nothing the trace itself does not.
    let total := counts.foldl (fun acc c => acc + (Lean.fromJson? (α := Nat) c).toOption.getD 0) 0
    if entries.isEmpty || total ≤ 1 then ""
    else s!"\nTrace depths: {", ".intercalate entries}"
  | _ => ""

/-- See the table on `SimulateResult` for the cases `#simulate` can produce. -/
private def formatSimulateResult (j : Json) : MessageData :=
  let suffix := fmtDepthHistogram j ++ fmtSeedSuffix j
  match fmtJson (j.getObjValD "result") with
  | "found_violation" => fmtViolation j suffix
  | "no_violation_found" =>
      if isNoInitialStatesTermination j then
        m!"✅ No initial states available after applying state constraints{suffix}"
      else
        m!"✅ No violation in {fmtJson (j.getObjValD "traces_run")} traces{suffix}"
  | "cancelled" => m!"⚠️ Cancelled{suffix}"
  | r => fmtUnexpected r j

private def formatSymbolicTraceResult (j : Json) : MessageData :=
  match fmtJson (j.getObjValD "result") with
  | "found_violation" => fmtViolation j
  | "no_violation_found" =>
      let trace := j.getObjValD "trace"
      if trace != .null then m!"✅ Satisfying trace found\n{formatTrace trace}"
      else m!"✅ No violation (explored {fmtJson (j.getObjValD "explored_states")} states)"
  | "cancelled" => m!"⚠️ Cancelled"
  | r => fmtUnexpected r j

/-- Render a result for the infoview, using the renderer for the command that
produced it. -/
def formatResult : ResultKind → Json → MessageData
  | .modelCheck, j => formatModelCheckResult j
  | .simulate, j => formatSimulateResult j
  | .symbolicTrace, j => formatSymbolicTraceResult j

end Veil.TraceDisplay
