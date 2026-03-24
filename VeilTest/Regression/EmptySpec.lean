import Veil

veil module EmptySpec

after_init {
  pure ()
}

invariant true

/--
warning: you have not defined any actions for this specification; did you forget?
-/
#guard_msgs in
#gen_spec

/--
info: ✅ No violation (explored 1 states)
-/
#guard_msgs in
#model_check interpreted {  }

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  inv_0 ... ✅
-/
#guard_msgs in
#check_invariants

-- /--
-- warning: no actions are defined; skipping trace query
-- -/
-- #guard_msgs(error, warning) in
-- sat trace {
-- }

-- /--
-- warning: no actions are defined; skipping trace query
-- -/
-- #guard_msgs(error, warning) in
-- unsat trace {
--   any 3 actions
-- }

end EmptySpec

veil module NoAfterInit

/--
error: no `after_init` block has been defined for this specification; every Veil module must have one
-/
#guard_msgs(error, warning) in
#gen_spec

end NoAfterInit
