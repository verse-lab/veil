# Working on Veil

Veil is a Lean library for specifying, testing, and verifying transition systems.
Start with the [README](README.md) for an overview and the [DSL reference](docs/DSL-Reference.md) for syntax.
The DSL frontend lives in `Veil/Frontend/`, the explicit-state model checker in
`Veil/Core/Tools/ModelChecker/Concrete/`, and shared utilities in `Veil/Util/`.
For proofs about Lean's built-in definitions, [Loogle](https://loogle.lean-lang.org/) can help find existing lemmas.

For TLA+-to-Veil translations and reviews, use the [translation skill](.agents/skills/tla-to-veil/SKILL.md).

## Implementation and testing

- When investigating a bug, reproduce it on the target branch with the smallest Lean example that still shows the failure. If it occurs in a dependency, isolate it there so the fix goes in the right repository.
- Add a regression in `VeilTest/` that fails before the fix and passes afterward. Exercise the user-facing command and check the behavior that was wrong. For example, if a trace reconstructed the wrong value, assert the expected value in the trace.
- After implementing a feature, run `lake build VeilTest` from the repository root to run all unit tests.
- Run the affected protocol examples in `Examples/` when changing DSL or verification behavior. Use `lake build Examples` for changes that cut across protocols. Update the relevant guide in `docs/` when the user-facing behavior changes.

## Pull requests

Title PRs using [Conventional Commits 1.0.0](https://www.conventionalcommits.org/en/v1.0.0/).
Match recent Veil commits by using a lowercase type and a short imperative description.
Prefer `type: description`.
Use `feat` for a feature and `fix` for a bug. Other types used here include `perf`, `refactor`, `docs`, and `chore`.

Two examples from Veil's history show this style.

- `fix: preserve bit-vectors during automatic hypothesis destruction`
- `feat: add live progress for #updr`

Keep each PR focused on one concern. Leave unrelated workspace edits out of the diff. When one change depends on another, use `gh stack` to organize the PRs in dependency order.

Link the issue when there is one. Structure the description of every bug-fix PR around these three points.

1. **Observed bug.** State what the user did, what happened, and what they expected. Include the minimal reproducer or diagnostic when it helps.
2. **Root cause.** Identify the code path or assumption that produced the failure. If the report exposed a broader problem, explain which other cases it affects.
3. **Solution.** Explain what changed and why it fixes the cause. Name the regression test and report the checks you ran.
