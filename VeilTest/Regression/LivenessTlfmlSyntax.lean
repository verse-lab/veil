module

public import Veil

/-!
# `liveness` formulas are written in `tlfml`

`liveness` reads Lentil's `tlfml` category, extended with `E(…)`, `T(…)` and `↔`, and checks it as an
`LTLLib.Formula` built by `[ltl| …]`.
-/

veil module LivenessTlfmlSyntax

individual x : Nat

#gen_state

after_init {
  x := 0
}

action step {
  require x < 3
  x := x + 1
}

-- `→` associates to the right, as in Lean: `x = 1 → (x = 2 → x = 3)` holds in the initial
-- state `x = 0`, whereas `(x = 1 → x = 2) → x = 3` does not.
temporal [impliesRight] ⌜ x = 1 ⌝ → ⌜ x = 2 ⌝ → ⌜ x = 3 ⌝
temporal [impliesLeft] (⌜ x = 1 ⌝ → ⌜ x = 2 ⌝) → ⌜ x = 3 ⌝
temporal (only := check) [iff] ⌜ x = 0 ⌝ ↔ ¬ ⌜ x ≠ 0 ⌝
temporal (only := check) [stepFair] □ (E(step) → ◇ T(step))
-- The only run is `x = 0, 1, 2, 3, 3, …`
temporal [nextIsOne] ◯ ⌜ x = 1 ⌝
temporal [belowUntilThree] ⌜ x < 3 ⌝ 𝑈 ⌜ x = 3 ⌝
temporal [zeroLeadsToThree] ⌜ x = 0 ⌝ ↝ ⌜ x = 3 ⌝

#gen_spec

/-- info: ✅ No liveness violation (checked 6 properties, explored 19 product states) -/
#guard_msgs in
#liveness_check [impliesRight] [iff] [stepFair] [nextIsOne] [belowUntilThree] [zeroLeadsToThree]
  interpreted {}

/--
error: ❌ Violation: liveness_failure (violates: impliesLeft)
  Stem:
    State 0:
      x = 0
    State 1:
      x = 1
    State 2:
      x = 2
    State 3:
      x = 3
  Loop (repeats):
    State 0:
      x = 3
-/
#guard_msgs in
#liveness_check [impliesLeft] interpreted {}

end LivenessTlfmlSyntax

/-! A formula without a model-checking counterpart is reported when the spec is finalized, which is
when the model-checking definitions of the temporal properties declared before `#gen_spec` are
generated. With `(only := check)`, this is an error. -/

veil module LivenessTlfmlUnsupported

individual x : Nat

#gen_state

after_init {
  x := 0
}

action step {
  x := x + 1
}

ghost relation positive := x > 0

temporal (only := check) [bare] ◇ positive
temporal (only := check) [weakFair] 𝒲ℱ step

/--
error: a plain term is not an atomic proposition of a model-checked property; write `⌜ positive ⌝` for a state predicate
---
error: a model-checked property can only use the atoms `⌜ … ⌝`, `⌞ … ⌟`, `E(…)` and `T(…)`, the fairness conditions `WF(…)` and `SF(…)`, the connectives `⊤`, `⊥`, `¬`, `∧`, `∨`, `→`, `↔`, `□`, `◇`, `◯`, `𝑈`, `↝` and `⇒`, and the quantifiers `∀ x, …`, `∀ x : T, …`, `∃ x, …` and `∃ x : T, …`; this formula is none of them
-/
#guard_msgs in
#gen_spec

end LivenessTlfmlUnsupported
