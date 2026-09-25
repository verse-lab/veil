#!/usr/bin/env python3
"""Keep core Veil independent of CSLib and the optional package in sync."""

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
EXTRA = ROOT / "VeilExtra"


def packages(directory):
    manifest = json.loads((directory / "lake-manifest.json").read_text())
    return {package["name"]: package for package in manifest["packages"]}


def main():
    core = packages(ROOT)
    extra = packages(EXTRA)
    forbidden = core.keys() & {"mathlib", "cslib", "VeilExtra"}
    if forbidden:
        raise SystemExit(f"Core Veil depends on optional packages: {sorted(forbidden)}")

    if (ROOT / "lean-toolchain").read_text() != (EXTRA / "lean-toolchain").read_text():
        raise SystemExit("Veil and VeilExtra must use the same lean-toolchain")

    # Both packages build the same checkout of Veil. Shared dependencies must
    # agree so switching between their workspaces does not change its imports.
    for name, package in core.items():
        other = extra.get(name, {})
        for field in ("type", "url", "rev", "subDir"):
            if package.get(field) != other.get(field):
                raise SystemExit(f"VeilExtra's {name} dependency disagrees on {field}")

    print("Package boundaries and shared dependency versions are consistent.")


if __name__ == "__main__":
    main()
