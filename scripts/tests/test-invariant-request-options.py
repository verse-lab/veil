"""Editing an option before a repeated check must change the published proof."""
from lean_lsp import ROOT, LeanServer

def main():
    path = ROOT / "VeilTest/Regression/InvariantRequestOptions.lean"
    source = path.read_text().replace(
        'if admitted then throwError "the retry reused the trusted proof"',
        'Lean.logInfo m!"published with sorryAx = {admitted}"',
    )
    with_option = "set_option veil.smt.trust false in"
    assert source.count(with_option) == 1
    server = LeanServer("invariant-request-options")
    try:
        server.initialize()
        for version, option in enumerate(("true", "false", "true"), 1):
            text = source.replace(with_option, f"set_option veil.smt.trust {option} in")
            uri = path.as_uri()
            if version == 1:
                server.open(uri, text)
            else:
                server.change(uri, version, text)
            diagnostics = server.diagnostics(uri, version, f"trust={option}")
            assert not any(d["severity"] == 1 for d in diagnostics), diagnostics
            assert any(d["message"].strip() == f"published with sorryAx = {option}"
                       for d in diagnostics), diagnostics
    finally:
        server.close()

if __name__ == "__main__":
    main()
