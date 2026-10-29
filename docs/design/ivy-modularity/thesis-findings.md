# Rabia isolates and invsets on the thesis branch

The inspected branch is `george-phd-thesis` at `25ff4ef866bdeaa893e9fb310a05f34759403aaa`. The GitHub branch endpoint and the local remote-tracking ref agreed on this commit. The design worktree remains based on current main at `eb458cb6`; these are features to port, not claims about that main baseline.

The branch changes the first recommendation from developing proof slices and reachable-invariant export to **porting, hardening and reusing the existing implementations**. In the selected API, `#gen_theorems` also performs reachable-invariant generation; the separate command below describes the historical implementation. The [modularity guide](../../Modularity-Guide.md) uses a module/isolate core; invsets remain available as local proof-support policies.

## Two implementations in the branch history

The earlier implementation used `open_isolate protocol`, `open_isolate wrapper1 with protocol`, `close_isolate`, and targeted check commands. It selected invariant hypotheses in an otherwise unchanged system. At historical commit `a434acf84bd494330d5dcfbbd2e876e8254b2bfe`, `getAllChecks` selects target clauses across all module actions, while the WP and transition tactics unfold supported invariant definitions and clear other folded invariants. [Target checks](https://github.com/verse-lab/veil/blob/a434acf84bd494330d5dcfbbd2e876e8254b2bfe/Veil/DSL/Check/Main.lean#L69), [proof-context restriction](https://github.com/verse-lab/veil/blob/a434acf84bd494330d5dcfbbd2e876e8254b2bfe/Veil/Tactic/Main.lean#L233).

The thesis head ports this idea to `invset` declarations, support resolution, and restricted dischargers. Rabia's `Protocol` and `Wrapper1` through `Wrapper5` use these groups directly. [Rabia declarations](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/Examples/Rabia/Rabia.lean#L164).

The current syntax is:

```lean
invset Protocol {
  invariant [local_fact] p
}

invset Wrapper extends Protocol {
  invariant [additional_fact] q
}

invset Selected extends Protocol := { local_fact, additional_fact }

#check_invariants Wrapper
#check_invariants Wrapper using Protocol
```

Here `p` and `q` stand for already declared predicates; this short syntax illustration is separate from the complete bridge program.

## Implemented semantics

| Mechanism | Implemented behavior | Source |
| --- | --- | --- |
| Targets and support | A group's targets are its directly declared or selected clauses. Support includes those targets and recursively the parents' support. Unknown clauses, unknown groups and cyclic inheritance are errors. | [InvSet representation](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/Veil/Frontend/DSL/Module/Representation.lean#L258), [resolver](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/Veil/Frontend/DSL/Module/Util/Assertions.lean#L80) |
| Explicit support | `using` replaces inherited parent support with the specified groups' resolved support, while retaining the target group's own clauses. | [Check resolution](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/Veil/Frontend/DSL/Module/Elaborators.lean#L466) |
| Unchanged theorem | Restricted WP and transition dischargers prove the ordinary VCs. Support changes their tactic scripts, not the VCs' statements. | [Restricted scripts](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/Veil/Frontend/DSL/Module/VCGen/Induction.lean#L318) |
| Enforcement | The tactic unfolds the assembled invariant conjunction, splits conjunctions, and attempts to clear invariant-headed hypotheses outside support before ordinary unfolding. | [Support enforcement](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/Veil/Frontend/DSL/Tactic.lean#L878) |
| Selected check | `#check_invariants Group` selects that group's invariant targets across initialization and actions. It excludes no-throw VCs. | [Target filter](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/Veil/Frontend/DSL/Module/Elaborators.lean#L398) |
| Default check | The default command supplies group support per target, includes standalone invariants, and includes no-throw checks. | [Default planning](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/Veil/Frontend/DSL/Module/Elaborators.lean#L427) |
| Initialization | Initializer targets use the ordinary unrestricted initialization discharger. They do not assume pre-state invariants. | [Discharger attachment](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/Veil/Frontend/DSL/Module/VCGen/Induction.lean#L356) |
| Reachability export | `#gen_reachable_invariants` checks that every required initialization/action transition theorem exists, proves the assembled invariant by induction on reachability, and exports each clause's `.is_inv` projection. It supports substitutions for module sorts. | [Availability check](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/Veil/Frontend/DSL/Module/ReachableInvariants.lean#L37), [generated induction](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/Veil/Frontend/DSL/Module/ReachableInvariants.lean#L199) |

Rabia ends with active `#check_invariants` and `#gen_theorems`. RabiaMore then invokes `#gen_reachable_invariants with phase := Nat, state_value := state_value` and uses the resulting lemmas in further Lean proofs. The README and an early comment about disabled proof recovery are stale; the active commands are stronger evidence. [Rabia exports](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/Examples/Rabia/Rabia.lean#L1943), [RabiaMore usage](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/Examples/Rabia/RabiaMore.lean#L57).

## What to reuse and harden

Reuse the `invset` declaration forms, separation of targets from support, default checking plan, support-restricted WP/TR scripts, theorem export and reachable-invariant generator. Keep proof groups orthogonal to component identity and environment contracts.

The existing support tactic uses `try clear`, selects invariant-headed facts rather than arbitrary theory assumptions, and does not constrain an independently supplied manual proof. It therefore does not certify that a result used only its stated support. Preserve the unchanged-theorem soundness advantage while adding strict exclusion diagnostics or support-only helper proofs, solver-query inspection, and provenance of preprocessing and fallback.

The regression `InvSetDefaultSupport.lean` checks that a restricted discharger is attached. Its expected successful `q := p` example has `q_true` in a group without a dependency on the group containing `p_true`. The reason for that success was not diagnosed here. Do not treat this test as proof of strict exclusion; add a test inspecting actual reduced obligations or query dependencies when porting. [Regression](https://github.com/verse-lab/veil/blob/25ff4ef866bdeaa893e9fb310a05f34759403aaa/VeilTest/InvSetDefaultSupport.lean#L17).

The reachable-invariant generator derives predicates over successful transitions. It checks for the required TR theorems rather than silently postulating missing clauses; trusted clauses without such theorems need explicit handling. It does not replace the separate no-throw obligation or make the default trusted-SMT mode reconstructed. Porting must preserve those distinctions.

This inspection did not build the thesis branch, which uses Lean 4.28. The semantic bridge witness accompanying the syntax proposal was independently checked using current main's Lean 4.32 toolchain.

## What remains new

Invsets do not supply module-instance ownership, checked method contracts, semantic frames, or preservation under autonomous foreign actions. Those obligations belong to the selected module/isolate core and theorem-backed summary tactics, without a separate state-observation or rely/guarantee declaration language. Monitor blocks and cross-instance calls remain optional later extensions.

The revised implementation order is:

1. Port invsets, folding reachable-invariant export into `#gen_theorems`; harden support enforcement and preserve all global obligations.
2. Use existing top-level module definitions and add isolate instantiation with explicit type/parameter bindings, retained bodies and proved frames.
3. Use checked `require`/`ensure` contracts and invset support to tune local and foreign-step invariant proofs.
4. Add monitor structuring and cross-instance calls only when an example needs them.

The Opus follow-up examined a source packet that included the `.is_inv` usage but not the generator body; this follow-up verifies the body and closes that open point. Its broad initialization argument is not adopted without additional conditions: a private initializer that reads observations may compute state sensitive to initialization order, even when writes are disjoint. The complete example avoids that problem by initializing each owned relation to a constant empty value and proving the actual ordered global initialization.
