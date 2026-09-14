#!/usr/bin/env python3
"""Reject mathlib in the resolved package graph and repository Lean imports."""
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
packages = json.loads((root / "lake-manifest.json").read_text())["packages"]
for package in packages:
    assert "mathlib" not in package["name"].lower(), package
    assert "mathlib" not in package.get("url", "").lower(), package
for directory in ("Veil", "VeilTest", "Examples"):
    for source in (root / directory).rglob("*.lean"):
        assert not re.search(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:Mathlib|LoomMathlib)(?:\.|\s|$)",
                             source.read_text(), re.MULTILINE), source
print(f"Checked {len(packages)} packages and all library, test, and example imports: no mathlib.")
