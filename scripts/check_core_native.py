#!/usr/bin/env python3
"""Audit the project produced by scripts/CoreModelSmoke.lean after it succeeds."""

import json
from pathlib import Path


project = Path(".lake/model_checker_builds/CoreModelSmoke")
packages = {
    package["name"]
    for package in json.loads((project / "lake-manifest.json").read_text())["packages"]
}
expected = {"Veil", "Loom", "proofwidgets", "aesop", "batteries"}
if packages != expected:
    raise SystemExit(f"Unexpected Core native dependencies: {sorted(packages)}")

link_inputs = (project / ".lake/build/bin/ModelCheckerMain.rsp").read_text()
for forbidden in (
    "cvc5", "/packages/smt/", "/packages/auto/", "/packages/Qq/",
    "/Verifier/", "/VCGen", "/Metadata", "/Backend/SMT/",
    "/Elaborators/Verification", "libVeil.a",
):
    if forbidden in link_inputs:
        raise SystemExit(f"Core native link includes {forbidden}")

print("Core native dependencies and link inputs contain no solver or verifier.")
