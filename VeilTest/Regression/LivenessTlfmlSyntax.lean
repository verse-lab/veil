module

public import Veil

/-!
# `liveness` formulas are written in `tlfml`

`liveness` reads Lentil's `tlfml` category, extended with `E(…)`, `T(…)` and `↔`.
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

ghost relation positive := x > 0

-- `→` associates to the right, as in Lean: `x = 1 → (x = 2 → x = 3)` holds in the initial
-- state `x = 0`, whereas `(x = 1 → x = 2) → x = 3` does not.
liveness [impliesRight] ⌜ x = 1 ⌝ → ⌜ x = 2 ⌝ → ⌜ x = 3 ⌝
liveness [impliesLeft] (⌜ x = 1 ⌝ → ⌜ x = 2 ⌝) → ⌜ x = 3 ⌝
liveness [iff] ⌜ x = 0 ⌝ ↔ ¬ ⌜ x ≠ 0 ⌝
liveness [stepFair] □ (E(step) → ◇ T(step))

/-- error: a `liveness` property is built from `⌜ … ⌝`, `E(…)`, `T(…)`, `⊤`, `⊥`, `¬`, `□`, `◇`, `∧`, `∨`, `→` and `↔`; this formula is none of them -/
#guard_msgs in
liveness [next] ◯ ⌜ x = 0 ⌝

/-- error: a plain term is not an atomic proposition of a `liveness` property; write `⌜ positive ⌝` for a state predicate -/
#guard_msgs in
liveness [bare] ◇ positive

#gen_spec

/-- info: ✅ No liveness violation (checked 3 properties, explored 6 product states) -/
#guard_msgs in
#liveness_check [impliesRight] [iff] [stepFair] interpreted {}

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
