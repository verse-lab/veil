"""Check missing Veil module ends and incremental recovery in the Lean server."""

from lean_lsp import ROOT, LeanServer


def trust_option_position(server, uri, session, line):
    """Read the verification widget's edit position through the same RPCs as the infoview."""
    cursor = {"line": line, "character": 2}

    def rpc(method, params):
        return server.send("$/lean/rpc/call", {
            "textDocument": {"uri": uri}, "position": cursor, "sessionId": session,
            "method": method, "params": params,
        }, True)

    widget, = rpc("Lean.Widget.getWidgets", cursor)["widgets"]
    refresh, = widget["props"]["html"]["element"][2]
    state = refresh["component"][2]["state"]
    # Version 1 is the initial "Loading..." text. The first update contains the results.
    updated = rpc("ProofWidgets.RefreshComponent.awaitRefresh", {"state": state, "oldIdx": 1})
    return updated["html"]["component"][2]["optionInsertPos"]


def check_reopened_trust_options(server, uri):
    source = """module
public import VeilTest.Regression.ImportedProofs.Spec
set_option warn.sorry false
set_option veil.smt.trust true

veil module Local
type node
relation r : node → Bool
after_init { r N := false }
action keep { pure () }
invariant [excluded] r N ∨ ¬ r N
set_option veil.deferVCGeneration true
#gen_spec
set_option veil.deferVCGeneration false in
#gen_spec
end Local

veil module NodeProofs -- first import
end NodeProofs

veil module Local
#check_invariants -- local
end Local

veil module NodeProofs
#check_invariants -- imported
end NodeProofs
"""
    server.change(uri, 10, source)
    diagnostics = server.diagnostics(uri, 10, "trust before reconstruction")
    assert not [d for d in diagnostics if d["severity"] == 1], diagnostics
    assert sum("Trusting SMT solver" in d["message"] for d in diagnostics) == 2, diagnostics
    session = server.send("$/lean/rpc/connect", {"uri": uri}, True)["sessionId"]
    lines = source.splitlines(keepends=True)
    insertions = []
    for check, setup in [("#check_invariants -- local", "set_option veil.deferVCGeneration false in"),
                         ("#check_invariants -- imported", "veil module NodeProofs -- first import")]:
        pos = trust_option_position(server, uri, session, lines.index(check + "\n"))
        assert pos == {"line": lines.index(setup + "\n"), "character": 0}, (check, pos)
        insertions.append(pos["line"])
    for line in sorted(insertions, reverse=True):
        lines.insert(line, "set_option veil.smt.trust false\n")
    server.change(uri, 11, "".join(lines))
    server.check(uri, 11, "reconstruction after applying widget edits")


def main():
    server = LeanServer("module-close")
    uri = (ROOT / "VeilTest" / "Regression" / "ModuleClose.lean").as_uri()
    source = "module\npublic import Veil\nveil module Editing\nnamespace Helper\n"
    try:
        server.initialize()
        server.open(uri, source)
        for version, closer in enumerate(["", "end Editing.Helper\n", "#exit\n", "end Helper\n", "end Helper\nend Editing\n"], 1):
            if version > 1:
                server.change(uri, version, source + closer)
            diagnostics = server.diagnostics(uri, version, f"edit {version}")
            errors = [d for d in diagnostics if d["severity"] == 1]
            if closer in ("", "#exit\n", "end Helper\n"):
                assert len(errors) == 1, diagnostics
                assert "Close it with `end Editing`" in errors[0]["message"], errors
                assert errors[0]["range"]["start"]["line"] == 2, errors
            else:
                assert not errors, diagnostics

        # Later editor snapshots can share the verifier started by this #gen_spec.
        # Removing a check must also remove the declarations its close would publish.
        spec = """module
public import Veil
veil module Editing
set_option veil.smt.trust false
individual flag : Bool
after_init { flag := false }
action keep { flag := false }
action other { flag := false }
invariant [off] flag = false
#gen_spec
"""
        for version, actions in enumerate([["keep"], ["other"], [], ["keep", "other"]], 6):
            checks = "".join(f"#check_action {action}\n" for action in actions)
            publication = "end Editing\nrun_meta do\n  let env ← Lean.getEnv\n"
            for action in ("keep", "other"):
                expected = str(action in actions).lower()
                publication += (
                    f"  unless env.contains `Editing.{action}_off == {expected} do\n"
                    f'    throwError "incorrect publication of {action}_off"\n'
                )
            server.change(uri, version, spec + checks + publication)
            server.check(uri, version, f"requested {actions}")

        check_reopened_trust_options(server, uri)
    finally:
        server.close()


if __name__ == "__main__":
    main()
