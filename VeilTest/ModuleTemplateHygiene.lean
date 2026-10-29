module

public import VeilTest.ModuleInstanceHelper

set_option veil.smt.trust false
set_option veil.printCounterexamples false

namespace TemplateDefinitionConstants
public abbrev sourceOffset : Nat := 4
end TemplateDefinitionConstants

open TemplateDefinitionConstants

veil module LexicalTemplate

type item
param base : Nat
param provider : InstanceSource item 0
individual stored : Nat

-- The caller will supply a parameter named n. This local n must not capture
-- that argument when base is specialized.
after_init {
  stored := (fun n : Nat => base + n + sourceOffset) 3
}

-- Both a formal module parameter and a state field can be shadowed locally.
procedure echo (base : Nat) {
  return base
}

procedure echo_field (stored : Nat) {
  return stored
}

action refresh {
  let result ← echo ((fun n : Nat => base + n + sourceOffset) 3)
  let result ← echo_field result
  stored := result
}

invariant [value] stored = base + 7

#gen_spec
end LexicalTemplate

namespace TemplateCallerConstants
public abbrev sourceOffset : Nat := 100
end TemplateCallerConstants

open TemplateCallerConstants

veil module LexicalTemplateComposition

type item
param n : Nat

isolate provider : InstanceSource (item := item) (capacity := 0)
isolate counter : LexicalTemplate (item := item) (base := n) (provider := provider) with provider

safety [caller_value] counter.stored = n + 7

#gen_spec

-- The template's instantiated predicate and the caller's predicate must
-- have identical meanings before any support selection or solver runs.
run_cmd do
  let mod ← Veil.getCurrentModule
  let some (_, owned) := mod.instanceNames.find? (·.1 == `counter.value)
    | throwError "missing instantiated invariant"
  let same ← Lean.Elab.Command.liftTermElabM do
    let left ← Lean.Meta.mkConstWithFreshMVarLevels (mod.name ++ owned)
    let right ← Lean.Meta.mkConstWithFreshMVarLevels (mod.name ++ `caller_value)
    Lean.Meta.withTransparency .all <| Lean.Meta.isDefEq left right
  unless same do
    throwError "template specialization changed the meaning of the caller's value predicate"

#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems

#check caller_value.is_inv

end LexicalTemplateComposition
