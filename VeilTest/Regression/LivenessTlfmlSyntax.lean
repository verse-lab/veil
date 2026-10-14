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
liveness [impliesRight] ⌜ x = 1 ⌝ → ⌜ x = 2 ⌝ → ⌜ x = 3 ⌝
liveness [impliesLeft] (⌜ x = 1 ⌝ → ⌜ x = 2 ⌝) → ⌜ x = 3 ⌝
liveness [iff] ⌜ x = 0 ⌝ ↔ ¬ ⌜ x ≠ 0 ⌝
liveness [stepFair] □ (E(step) → ◇ T(step))
-- The only run is `x = 0, 1, 2, 3, 3, …`
liveness [nextIsOne] ◯ ⌜ x = 1 ⌝
liveness [belowUntilThree] ⌜ x < 3 ⌝ 𝑈 ⌜ x = 3 ⌝
liveness [zeroLeadsToThree] ⌜ x = 0 ⌝ ↝ ⌜ x = 3 ⌝

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
when `liveness` properties are elaborated. -/

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

liveness [bare] ◇ positive
liveness [weakFair] 𝒲ℱ step

/--
error: a plain term is not an atomic proposition of a model-checked property; write `⌜ positive ⌝` for a state predicate
---
error: a model-checked property is built from the atoms `⌜ … ⌝`, `⌞ … ⌟`, `E(…)` and `T(…)` with `⊤`, `⊥`, `¬`, `∧`, `∨`, `→`, `↔`, `□`, `◇`, `◯`, `𝑈`, `↝` and `⇒`; this formula is none of them
-/
#guard_msgs in
#gen_spec

end LivenessTlfmlUnsupported
