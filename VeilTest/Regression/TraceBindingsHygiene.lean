module

public import Veil

/-! Query witnesses may shadow ordinary global names, but cannot shadow names
introduced by the module or by the generated state and theory wrappers. -/

veil module TraceBindingsHygiene

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action set_flag (value : Bool) {
  flag := value
}

action clear_flag {
  flag := false
}

invariant True

#gen_spec

-- Generated conjunctions and disjunctions must refer to their global constants,
-- while references in user assertions and arguments still name these witnesses.
#guard_msgs(drop info, drop warning) in
sat trace (And Or True False : Bool) {
  assert (And = true ∧ Or = false ∧ True = true ∧ False = false)
  set_flag And
  any action
  assert flag
}

#guard_msgs(drop info, drop warning) in
unsat trace (And Or True False : Bool) {
  assert (And = false ∧ Or = true ∧ True = false ∧ False = true)
  set_flag False
  assert (¬ flag)
}

-- ActionTag is a generated local binder, not a declaration in the module.
-- Allowing it here also makes its value disappear from reconstructed bindings.
/-- error: trace binding 'ActionTag' conflicts with a module or reserved trace name -/
#guard_msgs in
sat trace (ActionTag : Bool) {
  set_flag ActionTag
}

-- State wrappers expose the concrete field before its ordinary abstract view.
/-- error: trace binding 'flag_conc' conflicts with a module or reserved trace name -/
#guard_msgs in
sat trace (flag_conc : Bool) {
  set_flag flag_conc
}

-- Generated module declarations are reserved even when they are absent from
-- the module's table of declarations written by the user.
/-- error: trace binding 'State' conflicts with a module or reserved trace name -/
#guard_msgs in
sat trace (State : Bool) {
  set_flag State
}

/-- error: trace binding 'Theory' conflicts with a module or reserved trace name -/
#guard_msgs in
sat trace (Theory : Bool) {
  set_flag Theory
}

/-- error: trace binding 'Label' conflicts with a module or reserved trace name -/
#guard_msgs in
sat trace (Label : Bool) {
  set_flag Label
}

/-- error: trace binding 'FieldAbstractType' conflicts with a module or reserved trace name -/
#guard_msgs in
sat trace (FieldAbstractType : Bool) {
  set_flag FieldAbstractType
}

/-- error: trace binding 'relationalTransitionSystem' conflicts with a module or reserved trace name -/
#guard_msgs in
sat trace (relationalTransitionSystem : Bool) {
  set_flag relationalTransitionSystem
}

/-- error: trace binding 'A.x' must be an unqualified name -/
#guard_msgs in
sat trace (A.x : Bool) {
  set_flag A.x
}

end TraceBindingsHygiene
