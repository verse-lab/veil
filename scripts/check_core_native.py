#!/usr/bin/env python3
"""Audit native projects generated from both Core and full Veil sources."""

import json
from pathlib import Path
import sys


for name in sys.argv[1:] or ("CoreModelSmoke", "FullModelCompilation"):
    project = Path(".lake/model_checker_builds") / name
    packages = {
        package["name"]
        for package in json.loads((project / "lake-manifest.json").read_text())["packages"]
    }
    expected = {"Veil", "Loom", "proofwidgets", "aesop", "batteries"}
    if packages != expected:
        raise SystemExit(f"{name}: unexpected native dependencies: {sorted(packages)}")

    setup = json.loads((project / ".lake/build/ir/Model.setup.json").read_text())
    if setup["plugins"]:
        raise SystemExit(f"{name}: native model loads plugins: {setup['plugins']}")
    imports = setup["importArts"]
    if "Veil.Core" not in imports:
        raise SystemExit(f"{name}: native model does not import Veil.Core")
    for module in imports:
        if module in ("Veil", "Veil.DSL", "Veil.Frontend.DSL.Base") or any(
            module == prefix or module.startswith(prefix + ".")
            for prefix in (
                "Smt", "cvc5", "Auto", "Veil.Backend.SMT", "Veil.Core.Tools.Verifier",
                "Veil.Core.UI.Verifier", "Veil.Frontend.DSL.Module.VCGen",
                "Veil.Frontend.DSL.Infra.Metadata",
                "Veil.Frontend.DSL.Module.Elaborators.Verification",
            )
        ):
            raise SystemExit(f"{name}: native model imports {module}")

    link_inputs = (project / ".lake/build/bin/ModelCheckerMain.rsp").read_text()
    for forbidden in (
        "cvc5", "/packages/smt/", "/packages/auto/", "/packages/Qq/",
        "/Verifier/", "/VCGen", "/Metadata", "/Backend/SMT/",
        "/Elaborators/Verification", "libVeil.a",
    ):
        if forbidden in link_inputs:
            raise SystemExit(f"{name}: native link includes {forbidden}")

    print(f"{name}: native dependencies, imports, plugins, and link inputs are solver-free.")
