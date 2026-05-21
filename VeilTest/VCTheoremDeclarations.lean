import Veil

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

#check_invariants

#gen_theorems

#gen_theorems

run_cmd do
  let env ← Lean.getEnv
  unless env.contains `VCTheoremDeclarations.keep_excluded do
    throwError "expected invariant VC theorem to be added to the main environment"
  unless env.contains `VCTheoremDeclarations.keep_excluded_tr do
    throwError "expected alternative invariant VC theorem to be added to the main environment"
  unless env.contains `VCTheoremDeclarations.keep_doesNotThrow do
    throwError "expected doesNotThrow VC theorem to be added to the main environment"

end VCTheoremDeclarations

veil module VCTheoremDeclarationNameConflict

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

theorem keep_excluded : True := by
  trivial

#check_invariants

/--
error: cannot generate VC theorem `VCTheoremDeclarationNameConflict.keep_excluded` because a declaration with that name already exists with a different type
-/
#guard_msgs in
#gen_theorems

end VCTheoremDeclarationNameConflict

veil module VCTheoremDeclarationAlternativeNameConflict

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

theorem keep_excluded_tr : True := by
  trivial

#check_invariants

/--
error: cannot generate VC theorem `VCTheoremDeclarationAlternativeNameConflict.keep_excluded_tr` because a declaration with that name already exists with a different type
-/
#guard_msgs in
#gen_theorems

end VCTheoremDeclarationAlternativeNameConflict
