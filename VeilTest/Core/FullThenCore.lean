import Veil
import Veil.Core

veil module FullThenCore
individual flag : Bool
after_init { flag := false }
action toggle { flag := !flag }
invariant true
#gen_spec
run_cmd do
  unless ← Veil.hasVerificationSupport do throwError "full verification support is missing"
  unless (← Lean.getEnv).contains `FullThenCore.toggle.ext.wp do
    throwError "full action verification was not generated"
#guard_msgs(drop info) in
#check_invariants
end FullThenCore
