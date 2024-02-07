# State Transition Systems in Lean

We aim to build a _foundational_ framework for (1) specifying, (2) implementing,
(3) testing, and (4) proving safety and liveness properties of state transition
systems, with a focus on distributed protocols.

**Pay-as-you-go.** Recognising that interactive proofs are too labourious for
most projects, we aim to support a _progressive verification_ methodology, where
one can build assurance in the specified (and implemented) system in a gradual
fashion, via testing, model checking, automated verification (of a subset of
desired properties), and finally interactive verification.

**Automated reasoning.** The vision for this project is to become a suitable
substrate for many kinds of automated reasoning tasks related to state
transition systems, including but not limited to:

- invariant and temporal property inference
- model checking
- symbolic verification
- synthesis and repair
- compilation to executable code

**A better TLA+.** We aim to replace TLA+ as the language of choice for
modelling distributed systems. To enable this practically, we ought to be able
to represent all TLA+ specifications within our framework and support both
model-checking (akin to TLC) and proving them (akin to TLAPS).

## Questions

- To what extent we can _test_ such systems using QuickChick-style approaches?
- How to define STS in Lean such that we can discharge theorems using SMT?