# Veil Temporal Checker Guide

`#temporal_check` explores every infinite run of a finite instance of a Veil
module and checks the module's `temporal` properties on each of them. Its
docstring describes the command in detail; this guide covers fairness,
reading the results, and keeping checks small. Temporal properties are
described in [DSL-Reference.md](DSL-Reference.md#temporal-properties); the
arguments and execution modes shared with `#model_check` in
[ModelChecker-Guide.md](ModelChecker-Guide.md).

## Running the Checker

```lean
temporal [electsLeader]
  (∀ n, ∀ next, 𝒲ℱ (send n next)) ∧ (∀ s, ∀ n, ∀ next, 𝒲ℱ (recv s n next)) →
    ◇ ⌜ ∃ l, leader l ⌝

#temporal_check { node := Fin 3 }
```

The search runs on a single thread. Veil proves in Lean that its verdicts are
correct: if no violation is found, every run satisfies the property, and a
reported violation is a real run of the instance.

## Fairness

The checker includes runs that never take an enabled action, so most liveness
properties need fairness assumptions. Without the assumption on `recv`,
`electsLeader` is violated by a run that keeps sending.

## Reading the Result

| Output | Meaning |
| --- | --- |
| `✅ No liveness violation (checked N properties, explored M product states)` | Every run satisfies the N properties. M counts the states of the search's product of the system and the properties, not the system's states |
| `❌ Violation: liveness_failure (violates: p)` | A run violating `p`: a stem from an initial state, followed by a loop that repeats forever |
| `❌ Violation: assumption_failure (violates: a)` | The theory violates assumption `a`; nothing was explored |

The run is also shown in the trace widget.

## Keeping Checks Small and Fast

- The advice of the [Model Checker Guide](ModelChecker-Guide.md#keeping-searches-small-and-fast)
  applies.
- Fairness assumptions quantified over all arguments of an action grow with the
  instance: `∀ s, ∀ n, ∀ next, 𝒲ℱ (recv s n next)` is 27 assumptions for
  `Fin 3`. Assume fairness only for the actions that the property needs.
