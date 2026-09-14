import Veil

/-! A full-verification source must still compile its native model with Core. -/
veil module FullModelCompilation
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

#guard_msgs(drop info) in
#check_invariants

/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check compiled {} { allowed := .first } assumptions_hold_by decide

end FullModelCompilation
