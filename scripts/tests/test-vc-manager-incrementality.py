#!/usr/bin/env python3
"""Exercise VC manager checkpoint reuse through a real Lean language server.

Build VeilTest first, then run this script (Python standard library only).
--vc-manager and --multi-module select one regression; the default runs both.
By default the fixtures use ordinary @[veil] theorems. --compact replaces
their signatures with prove_veil_invariant_goal in the virtual document.
Only virtual documents are edited; evidence is retained in /tmp.
"""

import argparse

from lean_lsp import ROOT, LeanServer


def compact_proof(source, name, selector):
    start = source.index(f"@[veil]\ntheorem {name} ")
    end = source.index("  unveil\n", start) + len("  unveil\n")
    return source[:start] + f"prove_veil_invariant_goal {selector} using wp by\n" + source[end:]


def run_regression(multi_module, compact):
    name = "VCManagerMultiModuleIncrementality" if multi_module else "VCManagerIncrementality"
    fixture = ROOT / "VeilTest" / "Regression" / f"{name}.lean"
    uri = fixture.as_uri()
    source = fixture.read_text()
    if compact:
        if multi_module:
            source = compact_proof(source, "keep_trivial", "keep trivial")
        else:
            source = compact_proof(source, "initializer_bounded", "initializer bounded")
            source = compact_proof(source, "step_bounded", "step bounded")
    proof_kind = "compact" if compact else "theorem"
    server = LeanServer(f"{name}-{proof_kind}")
    try:
        server.initialize()
        if multi_module:
            server.open(uri, source)
            server.check(uri, 1, "fresh multi-module file")
            old = "  done\n"
            assert source.count(old) == 1, "missing unique first-module proof"
            source = source.replace(old, "  skip\n  done\n", 1)
            server.change(uri, 2, source)
            server.check(uri, 2, "edit proof in first module")
        else:
            start = source.index("-- BEGIN STEP PROOF\n")
            end = source.index("-- END STEP PROOF\n") + len("-- END STEP PROOF\n")
            without_proof = source[:start] + source[end:]
            # Establish that a missing manual proof is valid on a fresh open.
            server.open(uri, without_proof)
            server.check(uri, 1, "fresh file without proof")
            server.change(uri, 2, source)
            server.check(uri, 2, "insert proof")
            # #gen_spec and the initializer stay unchanged. The restored
            # checkpoint must not reuse the deleted step theorem as a witness.
            server.change(uri, 3, without_proof)
            server.check(uri, 3, "delete proof in one module")
        print(f"PASS: {name} ({proof_kind})", flush=True)
    finally:
        server.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--vc-manager", action="store_true")
    modes.add_argument("--multi-module", action="store_true")
    parser.add_argument("--compact", action="store_true",
                        help="use prove_veil_invariant_goal instead of explicit theorems")
    args = parser.parse_args()
    if not args.multi_module:
        run_regression(False, args.compact)
    if not args.vc_manager:
        run_regression(True, args.compact)


if __name__ == "__main__":
    main()
