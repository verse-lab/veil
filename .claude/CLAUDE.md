# Project: Veil

Veil is a Lean library focusing on specifying, testing and verifying transition systems. Please read [README.md](./README.md) to know the syntax of Veil specifications.

## Architecture

- `Examples/`: Veil specifications of many different protocols. If your task is to implement something for Veil, then usually you don't need to check this directory.
- `Test`: Test cases
- `Veil`: The source of Veil
  - `Veil/Frontend`: Related to the Veil specification syntax and semantics
  - `Veil/Util`: Some generic utilities, not very specific to Veil
  - `Veil/Core/Tools/ModelChecker/ConcreteNew`: Explicit-state model checker for Veil specifications
  - `Veil/Core/Tools/ModelChecker/Concrete`: **Deprecated, do not check this directory unless instructed**

## Important Notes

- If you need to write some proofs about some built-in Lean definitions, one good way is to search on [Loogle](https://loogle.lean-lang.org/). 
- Whenever you've finished implementing certain feature, remember to run `lake build Test` to go through all unit tests. 
