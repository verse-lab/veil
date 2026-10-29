# Ivy-style modular safety verification

The implementation uses existing top-level `veil module` definitions and `isolate name : Module (parameter := argument) with dependencies`. There is no assignment-style `=`, separate object syntax, action export declaration, or mandatory `specification` block. Veil's existing `action`/`procedure` distinction supplies exported and internal operations. `#check_invariants` performs verification, and `#gen_theorems` also derives reachable invariants.

The [modularity guide](../../Modularity-Guide.md) contains the complete executable DSL example, precise checking behavior, and supported scope. The three executable examples are [Bridge](../../../Examples/Modularity/Bridge.lean), [Counters](../../../Examples/Modularity/Counters.lean), and [SharedSource](../../../Examples/Modularity/SharedSource.lean).

## Evidence and decisions

The [Ivy and paper study](source-findings.md) records what is actually implemented at Ivy commit `8858a0241ed37141757b7a051acc24c58e49c2f3`, together with the paper's safety rules and their limits. The [thesis-branch study](thesis-findings.md) records the earlier Veil invset and reachable-invariant machinery used with Rabia. Baseline observations there describe the inspected commits, before this implementation.

The small core is boundary invariants, internal-call requirements, checked postconditions, interference preservation, and semantic frames. Ivy specification/implementation structuring and monitors are useful extensions, not prerequisites for this core. Veil can also obtain proof-context modularity directly through tactics, retaining the complete system theorem and restricting invariant support before automation. This reuses the useful thesis machinery while strengthening its support enforcement and proof-export checks.

The implementation therefore has two layers:

1. Concrete module occurrence specialization plus strict invariant proof views. Every externally scheduled action family remains in the system. Component contracts, initializer behavior, frames, and foreign-step preservation are checked over that concrete system.
2. Theorem-backed transition summaries that can discharge a concrete preservation obligation without unfolding the provider implementation. Entry premises and assertion freedom remain explicit. Initial summary extraction/application is manual Lean proof rather than an additional declaration language.

Occurrence specialization uses one root state with distinct generated field labels, avoiding ambiguous inference between multiple equal-type component embeddings. Definition-time syntax/name/typeclass capture and caller-argument pinning preserve the meaning of reused modules. Specialization is transactional, so a failed replay cannot leave a partial action table eligible for theorem export.

Astra and Opus reviews led to separate no-throw and summary obligations, semantic frame checks over actual bodies, definition-scope and lexical hygiene tests, exact dictionary bindings, and complete concrete transition coverage before reachable-state export. The implementation deliberately keeps safety separate from temporal composition: summaries that permit stuttering do not establish liveness or bounded response.
