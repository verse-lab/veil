# Model checking with `Veil.Core`

Use `import Veil.Core` for the Veil DSL and explicit-state model checking
without importing CVC5, SMT integration, VC generation, or the verification
manager/server:

```lean
import Veil.Core

veil module Toggle
individual flag : Bool
after_init { flag := false }
action toggle { flag := !flag }
invariant true
#gen_spec
#model_check interpreted {} {}
#model_check compiled {} {}
end Toggle
```

Core retains state and theory declarations, finite enumerations, custom
concrete representations, actions, procedures, relational transitions,
assumptions, invariants, and state constraints. Interpreted, compiled, and
automatic model-checking modes retain parallel search, progress reporting,
and counterexample traces. Ordinary Lean proofs and solver-free
`assumptions_hold_by` tactics remain available.

`#gen_spec` assembles the labels and assumptions needed for execution. It does
not generate verification conditions or start a verification manager. Runtime
assumptions, invariants, and assertion failures are still checked. Internal
Loom WP proofs needed by procedure elaboration and executable extraction
remain; external action WPs, transition weakening, and locality proofs are
skipped.

`#check_invariants`, `#check_action`, `#gen_theorems`, symbolic
`sat trace`/`unsat trace`, and `veil_smt` require `import Veil`. Core reports
that requirement explicitly. Importing full Veil alongside Core, in either
order, enables the full frontend for specifications declared in that file.

## Lake configuration

The default Veil package still provides full verification and declares its
SMT dependencies. Merely changing a Lean import does not remove those packages
from the default Lake dependency graph.

To consume only Core, pass `coreOnly` to the Veil dependency in your
`lakefile.lean`:

```lean
import Lake
open Lake DSL

package myModels

require veil from git "https://github.com/verse-lab/veil.git" @ "george/no-cvc5"
  with NameMap.empty.insert `coreOnly "true"

@[default_target]
lean_lib MyModels
```

This profile excludes lean-smt and its CVC5/Auto/Qq dependencies. It retains
Loom, Batteries, Aesop, and ProofWidgets. Node/npm are still needed to build
the model-checker widgets. Full `import Veil` is unavailable in this profile.

When working in the Veil repository, build the Core profile with:

```bash
lake -R -KcoreOnly=true build
```

Lake caches configuration options: use `-R` when switching profiles (and
`lake -R build` to return to full Veil).

Core and full Veil use separate build directories (`.lake/build-core` and
`.lake/build`) to prevent stale artifacts from crossing profiles. The Core
library explicitly lists its modules so native builds cannot pull in the
verification library through Lake's library-wide link inputs.

Compiled model checking automatically chooses this dependency profile when
the source imports only Core. The generated project preserves the source's
imports, requires only the solver-free packages, and links without CVC5.
Sources importing full Veil continue to use the full native build profile.

## Implementation boundaries

`Veil.Core` imports shared declaration elaborators, executable extraction,
and the concrete model checker. The existing full import paths add
verification support:

- `Frontend.DSL.Module.Elaborators.Core` handles declarations, Core spec
  finalization, and model-checking commands. `Elaborators.Verification` adds
  full finalization and verification commands.
- `Infra.VerificationSupport` defines the optional finalization interface.
  Full Veil supplies a declaration in the Lean environment, making capability
  detection import-scoped rather than process-global.
- Shared tactic support lives in `Frontend.DSL.Tactic.Core`. SMT tactics stay
  in `Frontend.DSL.Tactic`. Solver-free simplification and quantifier helpers
  live under `Frontend.DSL.Infra`; old SMT helper paths remain facades.
- Ordinary frontend state and assertion locations remain shared. Verifier
  channels and registration state live in `Core.Tools.Verifier.Environment`;
  SMT assertion reporting lives in `Core.UI.Verifier.AssertionErrors`.
- Enum axioms use Lean's `List.Nodup` under Core and the equivalent SMT
  `distinctN` predicate under full Veil.

The regression suite checks Core execution and counterexamples, unsupported
verification diagnostics, absence of generated verification declarations,
and both import orders. `scripts/CheckCoreImports.lean` audits the compiled
import closure and rejects SMT, CVC5, VC generation, verifier modules/state,
and unfinished Veil declarations. `scripts/CoreModelSmoke.lean` exercises
native compilation and execution without solver plugin flags.
`scripts/check_core_native.py` then checks the generated dependency manifest
and native link inputs for solver or verifier dependencies.
