#!/usr/bin/env python3
"""Exercise real SAT/UNSAT trace workers and document edits after building Veil.

Run python3 scripts/tests/test-trace-request-options.py. Each trace uses a
distinct, generous SMT timeout as its worker marker. The fixture observes the
actual SMT tactic configuration and runs the ordinary solver.
"""

from lean_lsp import LeanServer
from proof_reuse import ProofDocument, replace_once


def check_results(diagnostics, sat_witnesses, errors=()):
    messages = [d["message"] for d in diagnostics]
    problems = [d["message"] for d in diagnostics if d.get("severity") in (1, 2)]
    assert len(problems) == len(errors), problems
    assert all(any(msg.startswith(error) for msg in problems) for error in errors), problems
    witnesses = [msg for msg in messages if "Satisfying trace found" in msg]
    assert len(witnesses) == sat_witnesses, messages
    assert all("flag = true" in msg for msg in witnesses), witnesses


def run(server):
    doc = ProofDocument(server, "VeilTest/Regression/TraceRequestOptions.lean")
    source = replace_once(doc.path.read_text(), ":= none", doc.logged(":= some LOG"))
    queries = source[source.index("section\nset_option veil.smt.timeout 71"):source.index("end TraceRequestOptions")]

    fresh = doc.change(source, "original queries", lambda ds: check_results(ds, 1))
    assert {"71", "72"}.issubset(fresh), fresh

    # Run the same graph nodes again. Re-elaborating the surface syntax alone
    # can produce fresh trace VCs because generated binders carry macro scopes.
    retry_existing = """set_option veil.smt.timeout 69 in
run_cmd retryExistingTrace `reachable
set_option veil.smt.timeout 70 in
run_cmd retryExistingTrace `initialTrue
"""
    exact = doc.change(replace_once(source, "end TraceRequestOptions", retry_existing + "end TraceRequestOptions"),
                       "retry each original VC", lambda ds: check_results(ds, 1))
    assert {"69", "70"}.issubset(exact), exact

    edited = source.replace("timeout 71", "timeout 65").replace("timeout 72", "timeout 66")
    delta = doc.change(edited, "edit only the timeout on both traces", lambda ds: check_results(ds, 1))
    assert {"65", "66"}.issubset(delta), delta

    # Append the same named queries after their original workers have finished.
    def repeated(sat, unsat, flip=False):
        extra = queries.replace("timeout 71", f"timeout {sat}").replace("timeout 72", f"timeout {unsat}")
        if flip:
            extra = extra.replace("assert flag", "assert !flag")
        return replace_once(source, "end TraceRequestOptions", extra + "end TraceRequestOptions")

    retries = doc.change(repeated(73, 74), "repeat both checks with new options",
                         lambda ds: check_results(ds, 2))
    assert {"73", "74"}.issubset(retries), retries

    # Both kinds of query are deliberately wrong. Check their actual diagnostics
    # so the stale revision below is known to produce observable wrong results.
    wrong = doc.change(repeated(75, 76, flip=True), "opposite trace assertions",
                       lambda ds: check_results(ds, 1, ("No satisfying trace exists", "Counterexample found")))
    assert {"75", "76"}.issubset(wrong), wrong

    # Hold a wrong query open, change the document, and only release the old
    # worker after the new worker reaches SMT. Exercise each expected polarity.
    for sat, unsat, gate_id in [(77, 78, 77), (81, 82, 82)]:
        gate = doc.log.with_suffix(f".block-{gate_id}")
        gate.touch()
        try:
            before = len(doc.executions())
            doc.send(repeated(sat, unsat, flip=True))
            doc.wait_for(str(gate_id), since=before)
            doc.send(repeated(sat + 2, unsat + 2))
            doc.wait_for(str(gate_id + 2), since=before)
        finally:
            gate.unlink(missing_ok=True)
        doc.wait_for(f"finished-{gate_id}", since=before)
        ds = server.diagnostics(doc.uri, doc.version, "replace in-flight trace")
        check_results(ds, 2)
        assert {str(sat + 2), str(unsat + 2)}.issubset(doc.executions()[before:]), doc.executions()[before:]


if __name__ == "__main__":
    lsp = LeanServer("trace-request-options")
    try:
        lsp.initialize()
        run(lsp)
        print("PASS: trace request options")
    finally:
        lsp.close()
