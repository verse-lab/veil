module

public import Veil

veil module TransitionNegation
individual active : Bool
#gen_state

after_init { active := false }

action guarded {
  require active
  active := false
}

action conditional {
  require (if active then active else !active)
  active := if active then false else true
}

-- Guards should normalize to conjunctions, not existentials over proofs.
run_meta do
  for name in [``guarded.ext.tr, ``conditional.ext.tr] do
    let decl ← Lean.getConstInfoDefn name
    if (decl.value.find? (·.isAppOf ``Exists)).isSome then
      throwError "{name} contains an existential after transition normalization"

end TransitionNegation
