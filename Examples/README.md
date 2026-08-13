# Veil Examples

This directory contains protocol specifications written in [Veil](https://github.com/verse-lab/veil), organized by source and type.

## Directory Structure

### [Tutorial/](Tutorial/)

Extensively commented introductory examples: `Ring.lean` (leader election in a
ring, introducing Veil's syntax and commands) and `FloodSet.lean` (a complete
walkthrough of Veil's multi-modal workflow, from modelling through testing to
interactive proof). Start here if you're new to Veil. The `POPL26/` subfolder
contains the examples used in the POPL'26 tutorial, demonstrating different
type encodings of the ring protocol (decidable, finite, natural numbers).

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
lake lean Examples/Tutorial/Ring.lean
```

## Conventions

- File names use PascalCase (e.g., `TwoPhaseCommit.lean`)
- Each file declares a `veil module` matching the file name
- Each file imports only `Veil`
