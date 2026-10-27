---
name: tla-to-veil
description: Translate TLA+ specifications (a .tla module plus its TLC .cfg) into Veil specifications in Lean, or review an existing TLA+-to-Veil translation. Covers state and action mapping, keeping the source's structure (actions, constants, quantifiers), encoding choices and their model-checking cost, semantic traps (primed-variable dependencies, framing, CHOOSE, stuttering, deadlock), reporting Veil failures as minimal examples, validating the result against TLC through invariants, known violations, and distinct-state counts, and explaining the result in comments for readers who know TLA+ but not Lean. Use whenever the user wants to port, re-model, review, explain, or cross-check a TLA+ spec in Veil, even if they don't say "translate". Not for general Lean proofs or TLA+-only work.
---

# TLA+ to Veil

Produce a readable Veil specification with the same behaviors as the TLA+ model the user selected, plus evidence from TLC and Veil runs that it does. Translate the source as it is, bugs included; suggest fixes separately.

Veil's own documentation lives in the Veil repository (or, under `.lake/packages/veil/`, if Veil is used as a downstream project): `docs/DSL-Reference.md` covers the language, and `docs/ModelChecker-Guide.md` covers `#model_check`, including sets (`TSet`), `termination`, `state_constraint`, and field representations. `Examples/TLA/` holds existing translations, most quoting each TLA+ definition above its Veil counterpart; translation.md says which to read for which construct. If an API named here doesn't resolve in the user's Veil version, grep `Veil/` and `VeilTest/`. This skill adds what is specific to TLA+:

- [translation.md](references/translation.md): mirroring the source, semantic traps, encoding alternatives, and what to do when Veil misbehaves. Read before translating or reviewing.
- [validation.md](references/validation.md): checking the translation against TLC and reporting the results.
- [explaining.md](references/explaining.md): the comment above each `#model_check` that tells a reader what each argument stands for in the cfg and how to run the check. Read before delivering.

## 1. Pin down the source model

Read the `.tla`, the `.cfg` that will actually be used, and the modules they extend. Establish:

- What the cfg selects: `SPECIFICATION` or `INIT`/`NEXT`, constant and model values, operator overrides, `CONSTRAINT`/`ACTION_CONSTRAINT`, `SYMMETRY`/`VIEW`, invariants and properties, and the deadlock setting (TLC checks deadlock unless the cfg says `CHECK_DEADLOCK FALSE`).
- The scope. Veil actions and invariants cover finite safety checking; fairness and temporal properties (`WF`, `SF`, `~>`, `[]<>`) don't carry over, so list any you leave out.
- The actions `Next` is built from, with their parameters. The Veil file gets the same list.
- A state mapping from each TLA+ variable and constant to a Veil field or type, including domains, index shifts, sentinel values, and which constant sets the source also uses as values (`Cardinality`, `SUBSET`, iteration). Justify any state you add or drop (e.g. a derived variable).

Ask the user only about unresolved choices that change the semantics.

## 2. Translate

In outline (details in translation.md):

- Mirror the source: one Veil action per source action, with its name and its parameters' domains and guards; constants, operators, and `LET` bindings under the source's names; quantifiers and set operations written as such, not detoured through `toList` and `List.any`. Add nothing the source lacks, such as a `List` standing in for a set constant or a parameter that a `require` pins to one value.
- `Init` → `after_init`, keeping every allowed initial state. Helpers → `procedure`s or ghost definitions, since every `action` is a separately enabled step.
- TLA+ updates are simultaneous, Veil statements sequential: settle which right-hand sides read old vs. new values before ordering assignments.
- An omitted Veil assignment means `UNCHANGED`; an omitted primed TLA+ variable means "any value".
- Properties stay invariants. Moving one into `assume` or `require` hides its violations.

Start with the direct translation. Where a construct has several reasonable encodings, note the alternatives and why you chose one, labeling performance claims as measured or expected. Optimize only real bottlenecks, never by dropping nondeterminism or adding guards, and re-run the checks afterwards. Re-modeling, such as replacing quorums defined by cardinality with Veil's `Quorum` type, is a separate decision that needs its own argument.

## 3. Check against TLC

Follow validation.md. With parameters aligned on both sides, report each criterion as passed, failed, not run, or not applicable:

1. **Invariants agree**: corresponding properties hold (or fail) on both sides, and the run is non-vacuous (initial states exist, actions fire).
2. **Known violations reproduce**: if the source has a known invariant violation, Veil finds the corresponding one, and you can map the counterexample's states and actions.
3. **Distinct-state counts match**: for a one-to-one state encoding, complete runs report equal distinct (not generated) state counts.

These checks are evidence, not a proof of equivalence. Investigate mismatches; don't delete properties, add constraints, or change the algorithm to make counts agree.

After validation, you may tune execution and storage settings such as execution mode, `seenSet`, and field representations to improve time or memory use; follow Veil's `docs/ModelChecker-Guide.md`. Keep the model, instance, and checking scope fixed, rerun validation, and report the settings and measured effects.

## 4. Deliver

The Veil file, building without warnings and headed by a comment naming the source (pinned to a commit if it is public), the selected configuration, and the main encoding choices. Above each `#model_check`, a comment that maps its arguments to the cfg and says how to run it (explaining.md). With it, a short account of: the selected source, config, and scope; the state/action mapping; notable encoding choices; the validation table and the commands used; and remaining gaps (out-of-scope properties, unresolved mismatches, Veil failures with their minimal examples).

## Reviewing an existing translation

Run the same steps on the existing file, comparing it with the source definition by definition; translation.md's "Mirror the source" doubles as the checklist. Typical findings: a source action split into several, a parameter the source lacks, a `List` standing in for a set constant, quantifiers detoured through `toList`, a dropped `LET` or a substituted operator, and a missing `termination false` where the cfg checks deadlock.

For each finding, show the source next to the translation, then the fix. Also list what you keep and why (an equivalent form, a workaround for a reported Veil failure) and the alternatives you reject. After fixing, rebuild without warnings and rerun the checks. Update probes or harnesses that call renamed or merged actions, and the comments above each `#model_check` (explaining.md). Rerun rather than trust earlier validation notes, and flag claims in them that no longer hold.
