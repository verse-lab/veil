import Veil

-- An assertion whose body fails to elaborate is not registered in the module.
-- Previously, `#gen_spec` would then finalize the specification without it and
-- `#check_invariants` would report all-green, silently omitting the property.
-- Now `#gen_spec` refuses to finalize while failed assertion declarations exist.

veil module DroppedAssertion

type node

relation r : node → Bool

#gen_state

after_init {
  r N := false
}

action flip (n : node) {
  r n := true
}

/-- error: Unbound uncapitalized variable: N' -/
#guard_msgs in
invariant [uniqueness] r N ∧ r N' → N = N'

/--
error: cannot finalize the specification: the following assertion declaration(s) failed to elaborate: [uniqueness]
-/
#guard_msgs in
#gen_spec

end DroppedAssertion
