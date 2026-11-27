module

public import Veil

-- A section can have exactly the same header as its enclosing module.
veil module One
set_option veil.smt.trust false
section One
end One
section
end
individual flag : Bool
after_init { flag := false }
action keep { flag := false }
invariant [off] flag = false
#gen_spec
#check_action keep
section
/-- error: Unexpected name `One.«»` after `end`: The current section is unnamed -/
#guard_msgs (substring := true) in
end One.«»
run_cmd do
  for name in [`One.keep_off, `One.keep_off_tr] do
    if (← Lean.getEnv).contains name then throwError "invalid end published {name}"
end
namespace Helper
#gen_theorems
run_cmd do
  let env ← Lean.getEnv
  unless env.contains `One.keep_off && !env.contains `One.Helper.keep_off do
    throwError "early publication used the helper namespace"
-- Close both namespaces with one Lean command.
end One.Helper

run_meta do
  let axioms ← Lean.collectAxioms ``One.keep_off
  if axioms.contains ``sorryAx then
    throwError "closing the module published an admitted proof"

-- Closing a fresh module without a spec or a check needs no verifier.
veil module Two
/-- error: The specification of module Two has not been finalized. Please call #gen_spec first! -/
#guard_msgs in
#gen_theorems
end Two

namespace Ordinary
section
end
end Ordinary

-- Lean uses a bare end for an empty namespace header, including a Veil module.
veil module «»
set_option veil.smt.trust false
individual flag : Bool
after_init { flag := false }
action keep { flag := false }
invariant [off] flag = false
#gen_spec
#check_action keep
end

run_meta do
  for suffix in [`keep_off, `keep_off_tr] do
    let name := Lean.Name.mkSimple "" ++ suffix
    unless (← Lean.getEnv).contains name do throwError "bare end did not publish {name}"

-- Preparing a deferred spec in a helper scope must survive that scope closing.
veil module ScopedPreparation
set_option veil.deferVCGeneration true
set_option veil.smt.trust false
individual flag : Bool
after_init { flag := false }
action keep { flag := false }
action idle { pure () }
invariant [off] flag = false
temporal [alwaysOff] □ ⌜ flag = false ⌝
#gen_spec

namespace Helper
#guard_msgs (drop info) in
#check_action keep
end Helper

#guard_msgs (drop info) in
#check_action idle
end ScopedPreparation

run_meta do
  for name in [``ScopedPreparation.keep_off, ``ScopedPreparation.keep_off_tr,
      ``ScopedPreparation.idle_off, ``ScopedPreparation.idle_off_tr] do
    if (← Lean.collectAxioms name).contains ``sorryAx then
      throwError "unexpected sorryAx in {name}"
  unless (← Lean.getEnv).contains `ScopedPreparation.alwaysOff do
    throwError "missing temporal definition in the module namespace"
