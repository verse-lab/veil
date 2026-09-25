# VeilExtra

Optional integrations and examples for Veil. This is a separate Lake package
that depends on the parent Veil checkout. Its CSLib integration brings Mathlib;
core Veil, including `#gen_theorems`, has neither dependency.

From the repository root, build the bridges and Ring proof:

```sh
lake -d VeilExtra build
```

Run plain `lake build` at the repository root to build core Veil and its tests.
The two packages have separate manifests and dependency directories. CI builds
both packages independently on Linux and macOS and runs core Veil's tests.

In a Lean file inside this package, import the full simulation bridge with:

```lean
import VeilExtra
```

For narrower imports, use `VeilExtra.CSLib.TransitionSystem`,
`VeilExtra.CSLib.Simulation`, or `VeilExtra.CSLib.WeakSimulation`.
The declarations still extend `Veil.RelationalTransitionSystem` and use CSLib's
own simulation definitions.

See the [simulation guide](../docs/CSLib.md) and the
[Ring example](VeilExtra/Examples/Ring/README.md) for the proof interface.

When updating dependencies, update the core package first, then run
`lake -d VeilExtra update veil`. Keep both `lean-toolchain` files in sync and run
`python3 scripts/check-package-boundaries.py` from the repository root to check
the package boundary and shared dependency pins.
