import Veil
veil module Semantics
individual flag : Prop

#gen_state

after_init {
  flag := False
}

action set_flag = {
  assert False;
  flag := True;
}

action fail_nondeterministically (fail : Prop) = {
  if fail then
    assert False
    flag := True
  else
    flag := False
}

invariant True

/--
info: def Semantics.set_flag.ext : Wlp Mode.external State PUnit :=
fun s post => False
-/
#guard_msgs in
#print set_flag.ext

/--
info: def Semantics.set_flag.tr : State → State → Prop :=
fun st st' => False
-/
#guard_msgs in
#print set_flag.tr

#gen_spec

/- FIXME: those queries give different results. We will fix it once
   we implement the termination checker. -/
-- #check_invariants     -- fails
-- #check_invariants_tr  -- succeeds

/-- error: the goal is false -/
#guard_msgs in
sat trace {
  set_flag
} by bmc_sat

/-- error: the goal is false -/
#guard_msgs in
sat trace {
  set_flag
  assert (flag = True)
} by bmc_sat

/--
info:
interpreted sort Bool
-/
#guard_msgs(info, drop warning, whitespace:=lax) in
sat trace {
  fail_nondeterministically
  assert (flag = False)
} by bmc_sat

end Semantics
