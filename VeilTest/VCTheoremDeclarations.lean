module

public import Veil

veil module VCTheoremDeclarations

type node

relation r : node → Bool

#gen_state

after_init {
  r N := false
}

action keep {
  pure ()
}

invariant [excluded] r N ∨ ¬ r N

#gen_spec

#gen_theorems
run_cmd do
  if (← Lean.getEnv).contains `VCTheoremDeclarations.keep_excluded then
    throwError "published an unrequested theorem"

#guard_msgs (drop info, drop warning) in
#check_action keep

#gen_theorems

#gen_theorems

run_cmd do
  let env ← Lean.getEnv
  unless env.contains `VCTheoremDeclarations.keep_excluded do
    throwError "expected invariant VC theorem to be added to the main environment"
  unless env.contains `VCTheoremDeclarations.keep_doesNotThrow do
    throwError "expected doesNotThrow VC theorem to be added to the main environment"

#check_invariants

end VCTheoremDeclarations

veil module VCTheoremDeclarationNameConflict
set_option veil.smt.trust false

type node

relation r : node → Bool

#gen_state

after_init {
  r N := false
}

action keep {
  pure ()
}

invariant [excluded] r N ∨ ¬ r N

invariant [later] True

#gen_spec

theorem keep_excluded : True := by
  trivial

#guard_msgs (drop info, drop warning) in
#check_action keep

/--
error: cannot generate VC theorem `VCTheoremDeclarationNameConflict.keep_excluded` because a declaration with that name already exists with a different type
-/
#guard_msgs in
#gen_theorems

run_cmd do
  unless (← Lean.getEnv).contains `VCTheoremDeclarationNameConflict.keep_later do
    throwError "a name conflict prevented publication of a later valid witness"

end VCTheoremDeclarationNameConflict
