# Ring Examples

This directory contains several versions of the same ring leader-election
protocol, arranged to show different modeling choices.

## Files

`RingDec.lean` is the small abstract version. It leaves `node` uninterpreted and
requires `TotalOrder node` and `Between node` instances. The state is represented
as Boolean relations (`leader` and `pending`), and `send`/`recv` take explicit
node arguments. It includes model checking over `Fin 4` plus one satisfiable and
one unsatisfiable trace query.

`RingNat.lean` is the compact concrete-list version. Nodes are `Nat`s drawn from
an immutable `allNodes : List Nat`, with an immutable `nextNode : Nat -> Nat`.
Messages and leaders are stored as lists. This file keeps only the core protocol,
the `single_leader` safety property, and a basic `messages_nodup` invariant.

`RingAssumptions.lean` is the full proof-oriented Nat/list version where
`nextNode` is still supplied as immutable theory data. It adds ghost relations
for ring order (`lt`, `btw`, `isNext`), assumes the required facts about
`nextNode`, adds the full invariant set, and includes explicit `@[veil]`
theorems for the generated proof obligations. Its model check supplies both
`allNodes` and a concrete `nextNode`.

`RingTheorems.lean` removes `nextNode` as an external theory field. Instead,
`nextNode` is defined from `allNodes` using `List.next`, and ordinary Lean
theorems recover the facts that `RingAssumptions.lean` assumes. The Veil protocol
and invariants are otherwise the same full proof-oriented version. Its model
check only supplies `allNodes`.

## Progression

- `RingDec.lean`: abstract finite model using typeclass order/between structure.
- `RingNat.lean`: minimal concrete Nat/list model.
- `RingAssumptions.lean`: full concrete proof with successor behavior assumed.
- `RingTheorems.lean`: full concrete proof with successor behavior derived.

Run an individual example with:

```bash
lake lean Examples/Ring/<file>.lean
```
