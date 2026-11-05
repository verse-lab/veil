# Veil Examples

This directory contains protocol specifications written in [Veil](https://github.com/verse-lab/veil), organized by source and type.

## Directory Structure

### [Demo/](Demo/)

Introductory examples. Start here if you're new to Veil.

- [FloodSet/](Demo/FloodSet/): the FloodSet synchronous crash-fault agreement
  protocol. `FloodSet.lean` is the bare specification, `FloodSetCommented.lean`
  a complete commented walkthrough of Veil's multi-modal workflow (modelling,
  testing, invariant discovery, interactive proof), `FloodSetLiveness.lean`
  adds temporal properties checked by Lasso, and `FloodSetProgram.lean` writes
  the protocol as a per-node program in the distributed DSL.
- [Ring/](Demo/Ring/): leader election in a ring with different type
  encodings: decidable (`RingDec.lean`), finite (`RingFin.lean`), and natural
  numbers (`RingNat.lean`).

### [Ivy/](Ivy/)

Protocols from [IvyBench](https://github.com/aman-goel/ivybench) and similar
sources, using Ivy-style first-order encodings with uninterpreted types and
relations.

### [TLA/](TLA/)

Translations of [TLA+](https://github.com/tlaplus/Examples) specifications into
Veil. These use a wider range of Veil features including concrete types,
structures, and lists.

### [Synchronous/](Synchronous/)

Synchronous consensus protocols that operate in time-bounded rounds with
crash-fault tolerance.

### [Puzzles/](Puzzles/)

Recreational puzzles and brain teasers modelled as state machines (originally
from TLA+ examples). Useful for learning Veil's model checker.

## Building

```bash
# Build all examples
lake build Examples

# Build and check a single example
lake lean Examples/Demo/Ring/RingDec.lean
```

## Conventions

- File names use PascalCase (e.g., `TwoPhaseCommit.lean`)
- Each file declares a `veil module` matching the file name
- Each file imports only `Veil`
