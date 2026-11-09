#!/usr/bin/env python3
"""Check that all four commands send the renderer and its witness instantiation to the infoview.

Run after `lake build Veil`: python3 scripts/tests/test-state-visualizations.py
"""

from lean_lsp import LeanServer, ROOT

SOURCE = '''module
public import Veil

@[widget_module]
meta def probeRenderer : ProofWidgets.Component Veil.StateViewProps where
  javascript := "export default function probeRenderer() { return null; }"

veil module VisualizationProbe
param stepSize : Nat
type node
instantiate ringOrder : Between node
individual x : Nat
after_init { x := 0 }
action step {
  require stepSize = 1
  x := stepSize
}
assumption [three_nodes]
  ∃ a b c : node, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ ∀ d : node, d = a ∨ d = b ∨ d = c
invariant [zero] x = 0
temporal (only := check) [never_reached] ◇ ⌜ x = 2 ⌝
meta instance (inst : Instantiation) : StateViewTheory inst where
  fields := Lean.Json.mkObj [("configuredStep", Lean.toJson inst.stepSize)]

#set_visualizer probeRenderer
#gen_spec

set_option veil.violationIsError false
sat trace [takes_step] { step }
#set_visualizer "../../widget/js/dieHardVisualizer.js"
#check_invariants
#model_check interpreted { stepSize := Nat.succ 0, node := Fin 3 }
#temporal_check interpreted { stepSize := Nat.succ 0, node := Fin 3 }
end VisualizationProbe
'''


def component_props(html):
    if "component" in html:
        yield html["component"][2]
        for child in html["component"][3]:
            yield from component_props(child)
    if "element" in html:
        for child in html["element"][2]:
            yield from component_props(child)


def read_widget(rpc, pos):
    widgets = rpc("Lean.Widget.getWidgets", pos)["widgets"]
    assert len(widgets) == 1, widgets
    states = [p["state"] for p in component_props(widgets[0]["props"]["html"]) if "state" in p]
    assert len(states) == 1, widgets
    idx = 0
    while update := rpc("ProofWidgets.RefreshComponent.awaitRefresh", {"state": states[0], "oldIdx": idx}):
        idx = update["idx"]
        for props in component_props(update["html"]):
            if props.get("visualizer"):
                return props
    raise AssertionError("no completed result widget with a visualizer")


def main():
    server = LeanServer("state-visualization")
    uri = (ROOT / "VeilTest/Regression/StateVisualizationProbe.lean").as_uri()
    try:
        server.initialize()
        server.open(uri, SOURCE)
        session = server.send("$/lean/rpc/connect", {"uri": uri}, True)["sessionId"]
        diagnostics = server.diagnostics(uri, 1, "state visualization")
        assert not [d for d in diagnostics if d.get("severity") == 1], diagnostics

        visualizer = None
        renderer_sources = {
            "sat trace": "export default function probeRenderer() { return null; }",
            "#check_invariants": (ROOT / "widget/js/dieHardVisualizer.js").read_text(),
        }
        instantiation = {"node": "Fin 3", "stepSize": "1"}
        for prefix in ("sat trace", "#check_invariants", "#model_check", "#temporal_check"):
            pos = {"line": next(i for i, line in enumerate(SOURCE.splitlines()) if line.startswith(prefix)),
                   "character": 2}

            def rpc(method, params):
                return server.send("$/lean/rpc/call", {
                    "textDocument": {"uri": uri}, "position": pos, "sessionId": session,
                    "method": method, "params": params,
                }, True)

            props = read_widget(rpc, pos)
            if prefix in renderer_sources:
                visualizer = props["visualizer"]
                widget = rpc("Lean.Widget.getWidgetSource", {"hash": visualizer["hash"], "pos": pos})
                assert widget["sourcetext"] == renderer_sources[prefix], widget
            assert props["visualizer"] == visualizer, props
            if prefix in ("#model_check", "#temporal_check"):
                assert props["instantiation"] == instantiation, props
                theory = props["visualizationTheory"]
                assert theory["configuredStep"] == 1, theory
                between = theory["ringOrder.btw"]
                assert between["$veil"] == "set", between
                assert set(map(tuple, between["elements"])) == {(0, 1, 2), (1, 2, 0), (2, 0, 1)}, between
            elif prefix == "sat trace":
                assert props["result"]["trace"]["instantiation"] == instantiation, props
            if prefix == "#temporal_check":
                assert props["result"]["lasso"]["loop"][0]["$veil"] == "record", props
            elif prefix == "#check_invariants":
                counterexamples = [
                    cex["structuredJson"]
                    for vc in props["results"]["vcs"]
                    for discharger in vc["timing"]["dischargers"]
                    for cex in ((discharger.get("result") or {}).get("data") or {}).get("counterexamples", [])
                    if cex.get("structuredJson")
                ]
                assert any(cex.get("postState") for cex in counterexamples), props
                assert all(cex["instantiation"] == instantiation for cex in counterexamples), counterexamples
            else:
                states = props["result"]["trace"]["states"]
                assert [state["fields"]["fields"][0]["value"] for state in states] == [0, 1], props
            print(f"{prefix}: witness, instantiation, and registered widget available", flush=True)
    finally:
        server.close()


if __name__ == "__main__":
    main()
