import Veil.Core

/-! Run with `lake env lean scripts/CoreModelSmoke.lean`; no solver plugins are needed. -/
veil module CoreModelSmoke
enum node = { first, second }
immutable individual allowed : node
relation active (n : node)
assumption allowed = first
after_init { active N := false }
procedure activate (n : node) { active n := true }
action step {
  let n : node :| True
  require n = allowed
  activate n
}
invariant ∀ n, active n → n = allowed
#gen_spec
/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check compiled {} { allowed := .first } assumptions_hold_by decide
end CoreModelSmoke
