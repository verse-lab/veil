"""Check missing Veil module ends and incremental recovery in the Lean server."""

from lean_lsp import ROOT, LeanServer


def main():
    server = LeanServer("module-close")
    uri = (ROOT / "VeilTest" / "Regression" / "ModuleClose.lean").as_uri()
    source = "module\npublic import Veil\nveil module Editing\nnamespace Helper\n"
    try:
        server.initialize()
        server.open(uri, source)
        for version, closer in enumerate(["", "end Editing.Helper\n", "#exit\n", "end Helper\nend Editing\n"], 1):
            if version > 1:
                server.change(uri, version, source + closer)
            diagnostics = server.diagnostics(uri, version, f"edit {version}")
            errors = [d for d in diagnostics if d["severity"] == 1]
            if closer in ("", "#exit\n"):
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
        for version, actions in enumerate([["keep"], ["other"], [], ["keep", "other"]], 5):
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
    finally:
        server.close()


if __name__ == "__main__":
    main()
