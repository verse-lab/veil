# Explaining the translation to TLA+ readers

The user of this skill might know TLA+ and TLC well but probably not Lean. From the delivered file alone, they should be able to tell which cfg setting each part of a `#model_check` stands for, and how to run it. Put this in a comment directly above each `#model_check`. Separate the comment's parts with an empty `--` line.

## What the comment says, in order

1. **The TLC model.** Name the cfg, and the module TLC runs it on when that is not the spec itself (e.g. `MCPaxos.tla`). Say whether the check uses the cfg's instance. If it does not, say how it differs, e.g. "3 keys and 2 transactions, where the cfg has 2 keys and 3 transactions". Write "the cfg's instance", not "the same instance": the reader cannot tell what it is the same as.
2. **How to run it**, once per file. Lean runs every `#model_check` when it elaborates the file. In VS Code with the Lean 4 extension, the result appears in the InfoView while the cursor is on the command. From the project root, `lake env lean <path>` prints it. Above a commented-out check, add "uncomment it to run it".
3. **The outcome**, after you have run the check. Examples: "it finds a violation of `not_solved`, whose trace solves the puzzle; TLC reports `NotSolved` with the same steps", or "no violation, in as many distinct states as TLC (214)".
4. **The instantiation** (first `{ ... }` argument), which sets the module's `type`s and `param`s. Give one bullet per item: its values, and the cfg line it stands for, in the form `(cfg: Acceptors = {a1, a2, a3})`. Spell out index shifts and sentinels, e.g. "the processes are `0`, `1`, `2`, for TLA+'s `1`, `2`, `3`".
5. **Items that only satisfy an `instantiate` line**, such as `MsgSet := OrdList _`. One sentence is enough: "`OrdList` has the `TSet` instances that the `instantiate` lines above require."
6. **The theory** (second `{ ... }` argument), which sets the module's `immutable` fields, with the same bullets. If the module has `assumption`s, say that `#model_check` checks them before searching, and which `ASSUME` they translate.
7. **The rest of the cfg**, one bullet per line:
   - a model value: what stands for it, such as an `enum` constructor or `none` in an `Option`;
   - an `INVARIANT`: the Veil clause that checks it, or why none does (e.g. Lean's types ensure `TypeOK`);
   - a `CONSTRAINT`: its `state_constraint`, and that Veil does not check invariants on the states it drops;
   - the deadlock setting: the `termination` clause that matches it (translation.md);
   - `SYMMETRY`, `VIEW` and temporal `PROPERTIES`: Veil does not apply or check them.
8. **The options**, one plain sentence each on what they do: the mode (`compiled`, `interpreted`, or none), `maxDepth`, `sequential`, `seenSet`, `fingerprintType`, and `set_option veil.violationIsError false in` before an expected violation. Do not call an option faster or smaller: that depends on the instance and the machine.

Write one point per sentence, and state only what you have checked.

## Example

Adapted from `Examples/Puzzles/Prisoners.lean` in the Veil repository:

```lean
-- TLC checks this spec with `Prisoners.cfg`; the check below uses the cfg's instance.
-- Lean runs the check when it elaborates this file. In VS Code, the result appears in the
-- InfoView while the cursor is on `#model_check`. From the project root,
-- `lake env lean Examples/Puzzles/Prisoners.lean` prints it.
-- It finds no violation, in as many distinct states as TLC (214).
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `prisoner := Fin 4`: the prisoners are `0..3` (cfg: `Prisoner = {p1, p2, p3, p4}`).
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields:
-- * `Counter := 0`: prisoner `0` is the counter (cfg: `Counter = p1`).
-- * `cardPrisoner := 4`: the number of prisoners, TLA+'s `Cardinality(Prisoner)`. It must agree
--   with `prisoner` above. The cfg has no counterpart.
--
-- Before searching, `#model_check` checks these values against the `assumption` above, which
-- translates the spec's `ASSUME`.
--
-- The other settings of the cfg:
-- * `INVARIANT TypeOK`: `timesSwitchedlessEqual2` and `countBounded` above keep its bounds on
--   `timesSwitched` and `count`; Lean's types ensure the rest.
-- * `INVARIANT CountInvariant`: the `invariant [CountInvariant]` above.
-- * `PROPERTIES Safety`: `Safety == [](Done => ...)` holds when every reachable state satisfies
--   `Done => ...`, which the `safety [Safety]` clause above checks.
-- * `PROPERTIES Liveness`: the temporal property `<>Done`, which Veil does not check.
-- * The cfg has no `CHECK_DEADLOCK`, so TLC checks for deadlocks. With `termination false`
--   above, Veil also reports every state without successors as a deadlock.
-- Options:
-- * The check names no mode, so its search starts in Lean's interpreter and moves to a compiled
--   checker once that is built.
#model_check
{ prisoner := Fin 4 }
{ Counter := 0,
  cardPrisoner := 4 }
```

`Examples/TLA/` has comments for other cases: `Paxos.lean` (types that satisfy `instantiate`, a model value replaced by `Option`), `KVSnap.lean` (an expected violation), `LeaseGuard.lean` (a `CONSTRAINT`).

When the instance or the settings change, update the comment with them.
