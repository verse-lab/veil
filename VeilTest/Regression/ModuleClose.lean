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
end Two

namespace Ordinary
section
end
end Ordinary
