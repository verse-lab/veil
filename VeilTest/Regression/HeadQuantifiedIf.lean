module

public import Veil

veil module HeadForall

type node
relation r : node → Bool
individual done : Bool
#gen_state

after_init { r N := false; done := false }

action finish {
  if ∀ n, r n then
    done := true
}

invariant [marked] done → ∀ n, r n

#gen_spec

run_cmd do
  unless (← Lean.getEnv).contains `HeadForall.finish.ext.wp_local_eq do
    throwError "missing local WP equality theorem"
  unless (← Lean.getEnv).contains `HeadForall.finish.ext.tr_abstract do
    throwError "missing abstract transition theorem"

#check_invariants

end HeadForall

veil module HeadForallTyped

type node
relation r : node → Bool
individual done : Bool
#gen_state

after_init { r N := false; done := false }

action finish {
  if ∀ (n : node), r n then
    done := true
}

invariant [marked] done → ∀ (n : node), r n

#gen_spec

run_cmd do
  unless (← Lean.getEnv).contains `HeadForallTyped.finish.ext.wp_local_eq do
    throwError "missing local WP equality theorem"
  unless (← Lean.getEnv).contains `HeadForallTyped.finish.ext.tr_abstract do
    throwError "missing abstract transition theorem"

#check_invariants

end HeadForallTyped

veil module HeadExists

type node
relation r : node → Bool
individual done : Bool
#gen_state

after_init { r N := false; done := false }

action finish {
  if ∃ n, r n then
    done := true
}

invariant [marked] done → ∃ n, r n

#gen_spec

run_cmd do
  unless (← Lean.getEnv).contains `HeadExists.finish.ext.wp_local_eq do
    throwError "missing local WP equality theorem"
  unless (← Lean.getEnv).contains `HeadExists.finish.ext.tr_abstract do
    throwError "missing abstract transition theorem"

#check_invariants

end HeadExists

veil module HeadChoice

type node
relation r : node → Bool
individual done : Bool
#gen_state

after_init { r N := false; done := false }

action finish {
  if n :| r n then
    done := true
}

invariant [marked] done → ∃ n, r n

#gen_spec

run_cmd do
  unless (← Lean.getEnv).contains `HeadChoice.finish.ext.wp_local_eq do
    throwError "missing local WP equality theorem"
  unless (← Lean.getEnv).contains `HeadChoice.finish.ext.tr_abstract do
    throwError "missing abstract transition theorem"

#check_invariants

end HeadChoice
