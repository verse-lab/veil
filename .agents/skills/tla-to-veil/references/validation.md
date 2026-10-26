# Checking a translation against TLC

The aim is evidence that the Veil and TLA+ models have the same behaviors on small instances.

## Align the runs

Compare like with like:

| Dimension | Make equal |
| --- | --- |
| Domains | Sizes, ID shifts, interval endpoints, sentinel values, model-value equality |
| Constants | Values, quorums, operator overrides, how `CHOOSE` is resolved |
| Initial states | All allowed initial valuations, not one representative |
| Next | Actions, parameter domains, nondeterminism, atomicity, frames |
| Bounds | Message/log/ballot bounds, and how `CONSTRAINT` is encoded (translation.md) |
| Properties | Each TLA+ invariant ↦ a Veil invariant, including semantic parts of `TypeOK` |
| Search | Deadlock policy (as the cfg sets it; with a constraint, see translation.md), explicit stutter steps, no `SYMMETRY`/`VIEW` reduction, no depth bound |

Start with the smallest instance that exercises every action, then a second size or a boundary case sensitive to the encoding (e.g. size 1). Symmetry-reduced or `VIEW`-projected TLC counts aren't comparable to raw Veil counts.

If you supply custom instances, `Enumeration` must enumerate every value, `BEq` must agree with equality, and `Hashable` must assign equal values equal hashes. Otherwise, a run may miss behaviors or report misleading state counts.

## Steps

1. **Elaborate** the Veil file with `lake env lean File.lean`. Any `#model_check` in it runs at this point, so keep instances small, or use `#gen_executable` to check without searching. Expect no warnings; handle one that looks like a Veil bug as translation.md's "When Veil misbehaves" says. If the file sets `veil.deferVCGeneration`, elaborate once with it off as well.
2. **Spot-check risky actions** (old/new reads, aliasing, choice, indexing) on concrete states, by hand or with the [execution helpers](#using-the-action-execution-helpers). Check enabledness and expected successors, including all outcomes when branches overlap.
3. **Run both checkers to completion** with the same properties. For TLC: `java -cp tla2tools.jar tlc2.TLC -config M.cfg M.tla` (ask the user where the jar is if unclear). Confirm completion from the output, not from the exit status alone: TLC prints `Model checking completed` and `0 states left on queue`; Veil prints `✅ No violation (explored N states)`, but prints the same after a `maxDepth`-bounded search, so make sure none was set.
4. **Reproduce known violations** by running the buggy variant on both sides. Match the violated property and map the trace's states and actions; the traces needn't be identical (different allowed initial states or paths are fine). A violation of a different property, or a Veil assertion failure, is not a match.
5. **Compare distinct-state counts** only for a one-to-one encoding of reachable states and complete runs. Depth bounds, timeouts, or stopping at a violation leave incomplete counts; keep count runs and bug runs separate. If the encoding merges or duplicates states, explain the mapping instead of requiring equal raw counts.

Use targeted negative checks for high-risk rewrites, with a stated expected outcome. A deliberately false invariant failing at an initial state confirms initialization and invariant checking, not later action behavior. Check a guard rewrite against the successors it should enable or exclude. Report these as diagnostics, separately from reproducing a known violation, and revert temporary changes.

## Reading the numbers

- TLC's `distinct states found` corresponds to Veil's `explored N states`; TLC's `states generated` includes duplicates and pruned states.
- Generated counts include repeated generation of the same successor. Different choice or branch enumeration can change generated totals without changing the reachable state set.
- Both checkers include initial states in their generated totals; account for initialization when interpreting these totals.
- TLC counts `CONSTRAINT`-pruned successors as generated; Veil drops them before counting. This can change generated counts even when the retained distinct states agree.
- Disjunctive guards and multiple existential witnesses can generate the same successor more than once. Check how each tool enumerates the actual expression instead of assuming every disjunction has the same counting behavior.
- Zero initial states, suspiciously few states, or only self-loops need investigation even when no property fails.
- Equal counts don't imply equal state sets or edges. For more confidence on a tiny instance, compare the state sets through an explicit mapping.

For targeted count diagnostics, use separate temporary variants. A self-loop probe for pruned transitions must preserve the original choices and their multiplicities. Splitting a disjunctive guard can expose duplicate generation, but its results describe the diagnostic variant. Record the purpose and restore the source structure afterward.

## Diagnosing mismatches

| Symptom | Check first |
| --- | --- |
| Different initial counts | Missing `:= *`, different bounds, a constant turned into state or vice versa, sentinel values |
| Veil has fewer states | Missing branch or parameter values, extra guard, collapsed nondeterminism, a frame where TLA+ leaves the variable free |
| Veil has more states | `CHOOSE` made nondeterministic, a helper declared as an action, a missing frame, extra sentinel values, a non-canonical set encoding |
| Same count, different property result | Property translation, old/new reads, indexing |
| Known bug doesn't reproduce | Patched source variant, disabled action, invariant turned into `assume`/`require`, wrong property, incomplete search |

## Report

Keep an active `#model_check` for an instance compared with TLC in the delivered file, and identify that TLC run in a comment. Comment out other invocations with a reason.

One row per instance or variant. Mark each check as passed, failed, not run, or not applicable, and mark incomplete searches explicitly. Explain any count comparison that is not applicable. Use fresh runs rather than numbers from earlier validation notes.

| Instance (TLA+ / Veil parameters) | Both complete? | TLC distinct | Veil distinct | Invariants | Known violation | Deadlock policy |
| --- | --- | --- | --- | --- | --- | --- |

List the commands used. State conclusions at the strength the evidence supports: "elaborates", "agrees with TLC on these instances", or "count mismatch unresolved". Separate confirmed causes of count differences from untested explanations; leave unresolved cases explicit.

## Using the action-execution helpers

Veil provides these helpers for concrete probes; paths below are relative to the Veil repository:

- `Veil.Extract.extractAllResults` runs an already extracted computation on a theory and state (`Veil/Frontend/DSL/Action/Extract.lean`).
- Within a Veil module, `__veil_exec_action% inst theory state act` performs extraction and execution together; `#__veil_exec_action` prints the results (`Veil/Frontend/DSL/Module/Syntax.lean`).
- `VeilTest/ActionExecution.lean` provides result predicates such as `exactlyNSuccesses`, `hasSuccess`, and `hasNoExecutions`. See `VeilTest/ActionExecution/Nondeterminism.lean` for working examples.

For externally enabled actions, use `act.ext args`; raw calls treat `require` as a caller obligation. Build the probe from `initializer` and action calls, or use a procedure to set up the state and return the values to check. This avoids `.get?` reads tied to field representations. Check all expected nondeterministic outcomes, and confirm that a deliberately wrong expectation makes `#guard` fail.
