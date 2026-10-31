# Modular safety verification

Reusable components use the existing `veil module` form. An `isolate` declaration allocates a component instance and binds its types, immutable parameters, and references to existing instances. `action` supplies an externally scheduled step; `procedure` supplies an internal helper. Verification uses `#check_invariants`, and `#gen_theorems` exports both the checked verification conditions and their reachable-state consequences.

The core needs no `specification` block. Components express their assumptions with `require`, their checked postconditions with `ensure`, and their boundary properties with `invariant`. The `with` list selects other instances whose invariant facts support a component's proofs. All component actions remain in the composed transition system.

## Complete bridge example

This is the executable [bridge example](../Examples/Modularity/Bridge.lean). It models finalized transactions, an adapter's relay history, and a destination's mint history. Run `lake build +Examples.Modularity.Bridge` to verify it with proof reconstruction enabled.

```lean
module

public import Veil

set_option veil.smt.trust false

veil module Source

type tx
relation finalized : tx → Bool
after_init { finalized T := false }

action finalize (t : tx) {
  finalized t := true
  ensure ∀ u : tx, old(finalized u) → finalized u
}

#gen_spec
end Source


veil module Adapter

type tx
param source : Source tx

relation relayed : tx → Bool
after_init { relayed T := false }

procedure record (t : tx) {
  require source.finalized t
  relayed t := true
  ensure ∀ u : tx, relayed u ↔ old(relayed u) ∨ u = t
}

action relay (t : tx) {
  require source.finalized t
  record t
  ensure ∀ u : tx, old(relayed u) → relayed u
}

invariant [relay_backed]
  ∀ t : tx, relayed t → source.finalized t

#gen_spec
end Adapter


veil module Destination

type tx
param adapter : Adapter tx

relation minted : tx → Bool
after_init { minted T := false }

action mint (t : tx) {
  require adapter.relayed t ∧ ¬ minted t
  minted t := true
}

invariant [mint_backed]
  ∀ t : tx, minted t → adapter.relayed t

#gen_spec
end Destination


veil module Bridge

type tx

isolate source : Source (tx := tx)
isolate adapter : Adapter (tx := tx) (source := source) with source
isolate destination : Destination (tx := tx) (adapter := adapter) with source, adapter

safety [backed]
  ∀ t : tx, destination.minted t → source.finalized t

#gen_spec
#check_invariants
#gen_theorems
#check backed.is_inv

end Bridge
```

`param source : Source tx` declares a live reference to an existing `Source` instance with the specified transaction type. Binding it to `source` shares that instance's state and actual parameter bindings. It does not allocate another source or snapshot its history. Every type and ordinary parameter of the target module must be bound by name. Dependencies must appear before their users, and referenced instances must appear in the user's `with` list. Module names follow Lean namespace lookup; qualify an ambiguous or shadowed name explicitly.

The final property follows from the adapter and destination invariants. Their preservation includes autonomous environment steps: source finalization must preserve the adapter's invariant, and adapter relay must preserve the destination's invariant. No scheduling assumption hides those steps. An action that retracts finalization can invalidate the adapter's invariant and is rejected; see the [revocation regression](../VeilTest/ModularityRevocation.lean).

`require source.finalized t` is an external action guard when the environment schedules `relay`. At an internal call of `record`, `require` is a proof obligation. `ensure` is checked against the concrete body in both modes, at the point where it occurs. A terminal `ensure` describes the exit state; a branch-local or earlier check is not automatically an unconditional exit guarantee. `old(e)` evaluates `e` in that invocation's entry state; nested calls have distinct snapshots. Early returns that bypass an `ensure` are rejected. Final pure returns are supported. Contract expressions cannot contain nested action effects, and neither can the final return of a body containing `ensure`.

Invariants hold at external action boundaries. Internal procedures do not acquire a fresh invariant assumption at each call. Their standalone contract obligations use their explicit requirements and the module's immutable theory assumptions. An external action contract may use its selected boundary invariants; its generated theorem retains the invariant precondition.

## Instances, initialization, and frames

[TwoCounters](../Examples/Modularity/Counters.lean) instantiates the same module with limits 2 and 3. Each occurrence owns distinct state, even when all its types match another occurrence's types. [SharedSource](../Examples/Modularity/SharedSource.lean) binds two adapters to one source and verifies that both relay histories remain backed by that source.

Each component initializer runs once, in isolate declaration order. Its helper calls retain initializer guard semantics. The assembled initializer must establish all invariant clauses without assuming pre-state invariants. Component methods and initializers also receive semantic frame obligations: their actual bodies must preserve every mutable field outside that occurrence, including fields declared directly by the composition. This catches foreign mutations hidden behind Lean helpers as well as direct writes.

Template specialization preserves definition-time name resolution, macro expansion, elaboration options, and typeclass search. Instantiation arguments are checked in the caller's scope and pinned before insertion. Lexical binders are renamed to prevent capture. Explicit dictionary arguments preserve distinct bindings even for repeated requirements with the same class type.

## Proof views as tactics

`#check_invariants adapter` selects the adapter's invariant targets across initialization and every external action family. It also checks the global assertion-freedom, contract, and frame obligations. The default `#check_invariants` adds all remaining invariant targets. Reachable-state export requires the full set of global obligations, even after a selected check.

`with source` makes source invariants available to the adapter's proofs and retains source code. It does not replace source actions by an abstract transition. Thus this first layer implements proof-context modularity: the theorem still concerns the complete concrete system.

The lower-level `invset` interface supports the same technique without declaring component instances:

```lean
invset SourceFacts {
  invariant [source_clear] source_bit = false
}
invset SinkFacts extends SourceFacts {
  invariant [sink_clear] sink_bit = false
}
```

Here the state fields and actions are declared normally; the [complete invset regression](../VeilTest/InvSets.lean) shows initialization, checks, and theorem export. Explicit target lists use `invset Selected extends SourceFacts := { sink_clear }`.

Each target's discharger proves a stronger verification condition whose pre-state invariant contains only the selected support. A kernel-checked weakening then proves the original full-system condition. There is no unrestricted retry. An unrelated `False` invariant therefore cannot rescue a failing restricted proof. Theory assumptions remain part of the module's stated environment. When several groups target the same clause, their support is intersected so a cached proof is valid for every view. Per-command `using` overrides are rejected because the cache does not yet track separate support policies.

## Certified transition summaries

The next layer can avoid unfolding a provider's implementation. [Contracts.lean](../Veil/Frontend/DSL/Action/Semantics/Contracts.lean) defines:

- `TransitionSummary concrete precondition guarantee`: every successful concrete step satisfying the entry premise meets the guarantee.
- `ActionSummary act precondition guarantee`: the successful-step summary plus a separate assertion-freedom proof.
- `ProcedureContract proc precondition postcondition`: an internal contract retaining its return value and entry snapshot.

`TransitionSummary.preserves` proves the original concrete preservation condition using a provider certificate. The client must establish its entry premises and show that the guarantee preserves its target. Frames can be conjuncts of the guarantee.

The [complete certified-summary example](../VeilTest/CertifiedSummaries.lean) proves source growth and a frame once, then proves the adapter's foreign-step condition by applying that certificate without unfolding source finalization. Summary creation and application are explicit Lean proofs in this version; the DSL does not yet automatically turn `ensure` clauses into reusable summaries. Successful-step inclusion alone supplies no assertion-freedom or progress result.

## Theorem export

After `#check_invariants`, run `#gen_theorems`. It exports available VC proofs, derives `Invariants.is_inv` by induction on concrete reachability, and projects each named clause to its own `.is_inv` theorem. For example, `Bridge.backed.is_inv` quantifies over the bridge's transaction type and states the property for every reachable state of the assembled relational transition system.

`#gen_theorems with node := Nat` specializes module sorts when exporting reachable-invariant theorems. It does not start checks that were never requested. After a partial check it can export available VC lemmas but diagnoses missing obligations and withholds the global invariant theorem. Deferred checks, failed frames/contracts, omitted transition families, and admitted proofs in reconstruction mode cannot silently produce a global certificate.

The examples set `veil.smt.trust false`, so their proofs are reconstructed and checked by Lean. The existing explicit `veil.smt.trust true` mode retains its existing trust policy.

These theorems are conditional on concrete reachability under the stated theory assumptions. They do not establish that those assumptions are consistent or that initialization admits a state: contradictory assumptions or unsatisfiable initializer guards can leave the reachable set empty. The finite [model-checking regression](../VeilTest/ModularityModelCheck.lean) exercises the executable bridge, counters, and shared-source examples and witnesses their nonempty initial behavior.

## Current scope

This implementation handles safety of a concrete composition. It does not transfer LTL liveness, fairness, or response-time bounds. Those require additional scheduling, termination, time, and refinement arguments.

Use top-level module definitions and instantiate their leaf components explicitly. Nested composed-module instantiation and cross-instance procedure calls are not supported yet; dependency state reads are supported. Unsupported custom binding syntax, runtime syntax quotations, unsafe class-producing type specialization, and other unsupported template constructs fail with diagnostics instead of being replayed with a changed meaning.

For the source study and design rationale, see the [design notes](design/ivy-modularity/README.md).
