module

public import Veil

/-! A reconstructed trace must show its persistent witnesses and the actual
explicit action arguments, even when a default value would differ. -/

veil module TraceBindingWitness

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action set_flag (value : Bool) {
  flag := value
}

invariant True

#gen_spec

/--
info: ✅ Satisfying trace found
  Bindings:
    chosen = true
  State 0 (via init):
    flag = false
  State 1 (via set_flag(value=true)):
    flag = true
-/
#guard_msgs(info, drop warning) in
sat trace [chosen_true] (chosen : Bool) {
  set_flag chosen
  assert flag
}

/--
info: ✅ Satisfying trace found
  State 0 (via init):
    flag = false
  State 1 (via set_flag(value=true)):
    flag = true
-/
#guard_msgs(info, drop warning) in
sat trace {
  set_flag true
  assert flag
}

end TraceBindingWitness
