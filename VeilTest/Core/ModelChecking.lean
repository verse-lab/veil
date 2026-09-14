import Veil.Core

/-! These tests must elaborate in a process importing only the Core frontend. -/
veil module CoreModelChecking

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

run_cmd do
  let env ← Lean.getEnv
  for n in #[`Veil.fullVerificationSupport, `Veil.Verifier.vcManager,
      `CoreModelChecking.step.ext.wp, `CoreModelChecking.step.ext.tr_abstract,
      `CoreModelChecking.Invariants, `CoreModelChecking.ActionTag] do
    if env.contains n then throwError "Core generated verification declaration {n}"

/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check interpreted {} { allowed := .first } (sequential := true)

/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check interpreted {} { allowed := .first }
  (parallelCfg := some { numSubTasks := 2, thresholdToParallel := 0 })
  assumptions_hold_by decide

/-- error: ❌ Violation: assumption_failure (violates: assumption_0) -/
#guard_msgs in
#model_check interpreted {} { allowed := .second }

end CoreModelChecking

veil module CoreAssertionFailure
individual flag : Bool
after_init { flag := false }
action fail_assert { assert flag }
invariant true
#gen_spec

#guard (__veil_exec_action% {} {} { flag := false } fail_assert).any fun
  | .assertionFailure _ _ => true
  | _ => false

end CoreAssertionFailure

/-! Unsupported verification must fail explicitly rather than being skipped. -/
/-- error: Verification requires `import Veil`; `Veil.Core` supports explicit-state model checking. -/
#guard_msgs in
#check_invariants

/-- error: Verification requires `import Veil`; `Veil.Core` supports explicit-state model checking. -/
#guard_msgs in
#check_action step

/-- error: Verification requires `import Veil`; `Veil.Core` supports explicit-state model checking. -/
#guard_msgs in
#gen_theorems

/-- error: Symbolic traces require `import Veil`; use `#model_check` with `Veil.Core`. -/
#guard_msgs in
sat trace { any action }

/-- error: SMT verification requires `import Veil`. -/
#guard_msgs in
example : True := by veil_smt
