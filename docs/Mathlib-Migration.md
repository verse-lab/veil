# Building Veil without mathlib

Veil uses Loom's `george/v4.32.0-for-veil-no-mathlib` branch and Lean 4.32.0.
The lockfile pins the Loom commit. Run `lake build`; the former
`lake exe cache get` step is no longer needed.

Loom and lean-smt supply the semantics and SMT integration. Batteries, Aesop,
and ProofWidgets are explicit dependencies for library utilities, proofs, and
the existing UI. Qq, lean-auto, and lean-cvc5 remain dependencies of lean-smt.
Neither the main package nor the generated compiled model-checker package
requires mathlib.

## Lean API changes

The Veil DSL retains its commands and concrete representations. Supporting
Lean code may need changes:

- Use `Veil.Enumeration` for complete executable candidate lists. Lists retain
  their order and duplicates, including lists used for nondeterministic choice.
- Use `Veil.FinEncodable` for a bijection with `Fin n`. Specialized encodings
  remain available. The generic encoding removes duplicate candidates, retaining
  their last occurrences. Finite function equality checks the enumerated domain.
- Equivalences belong to `Veil.Equiv`; outside the namespace, use
  `open scoped Veil` for `≃`. Constructor enumeration and proxy deriving are
  implemented locally and no longer generate a mathlib `Fintype` instance.
- Assertion order belongs to `Loom.Order`. Use `open scoped Loom.Order` and
  `≤`, `⊤`, `⊥`, `⊓`, and `⨅` for assertions. Numeric comparisons in that scope
  fall back to Lean's ordinary relation. Continuations belong to `Loom.Cont`.
- Write `theorem`, `Nat`, and `Int` instead of relying on mathlib's command
  settings and numeric notation. Bundled proofs use core tactics or explicitly
  imported standalone tactics.

Quorum and Byzantine-node-set proofs now count filtered lists of unique
finite indices. The Stellar Consensus example represents its mathematical
sets with predicates local to that example. No finite-set library is required.
The snapshot-isolation examples use Veil's list permutations, preserving the
previous ordering and duplicate permutations.
The small elaborators adapted from mathlib retain their license and attribution
in their source files.

## Checks

After building, run:

```sh
lake build VeilTest
python3 scripts/check_no_mathlib.py
lake env lean --run scripts/CheckNoMathlib.lean
lake script run perftest
```

The source/package check includes bundled examples. The compiled audit checks
Veil's imported modules and rejects unfinished compiled Veil declarations.
The standalone regression suite covers candidate order, duplicate candidates,
empty domains, finite functions, constructor derivation, and quorum counts.

## Migration validation

`lake build Veil VeilTest` passes, including the standalone finite-type and
permutation regressions. The dependency audit checks eight resolved packages;
the compiled import/proof audit checks 9,813 Veil declarations.
These checks also pass after updating Loom to `294dc76ef35aea33af4fd25cde9f3a5d5dd73931`.
The update restores conventional scoped assertion notation and reuses Lean's
standard order laws. Veil's semantic and generated proofs now use Loom's public
pointwise-order lemmas, and the WP helper uses `Nat.ble` for its Boolean test.

The generated native model-checker package also has no mathlib dependency.
A compiled Boolean-toggle model runs successfully and explores two states.
On this workspace, cached cvc5 archives require the host glibc together with
Lean's C++ libraries and `lld`; a temporary `LEAN_CC` wrapper supplied those
linker settings. No repository build settings were changed for this workaround.

45 of the 47 example files pass source elaboration (using model-compilation
mode for model-checking examples). This checks generated model code without
running every exhaustive search; the FloodSet and Ring tutorial checks stop
at the model-check command, as native generation does. Two failures reproduce
on the original branch: Raft passes a deferred `do` block to `filterM`, which
the action elaborator rejects, and VerticalPaxosFirstOrder uses stale generated
proof signatures. These examples retain those existing limitations.

The NOPaxos and Suzuki–Kasami performance checks pass their 25-second and
15-second limits (13 and 6 seconds in this workspace). `PickPerf` completes
with the expected state counts but exceeds its 10-second limit on this machine:
13.55 seconds after the Loom update, versus 17.7 seconds before the update
and 24.1 seconds on the original branch.
The timeout is unchanged.
