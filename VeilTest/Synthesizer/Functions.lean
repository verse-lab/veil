module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! Functions as state: binary functions between nodes, functions into an enum, and functions into
`Int`. The decoder reads each as a total map from argument tuples to values. -/

veil module BinFun

type node
function f : node → node → node
individual bad : Bool

#gen_state

after_init {
  f X Y := X
  bad := false
}

action set (a b : node) {
  f a b := a
}

action trip (a b : node) {
  require f a b ≠ a
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

/--
Certified: theorem BinFun.ic3_safe (strengthening BinFun.ic3_inv)
-/
#guard_msgs(info, substring := true) in
#updr (expect := invariant) certify

end BinFun

veil module BinFunBug

type node
function f : node → node → node
individual bad : Bool

#gen_state

after_init {
  f X Y := X
  bad := false
}

action set (a b c : node) {
  require a ≠ c
  f a b := c
}

action trip (a b : node) {
  require f a b = b ∧ a ≠ b
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

/--
f: (0,0)↦0 (0,1)↦0 (1,0)↦0 (1,1)↦1
-/
#guard_msgs(info, substring := true) in
#updr (expect := unsafe) certify

end BinFunBug

veil module EnumFun

type node
enum phase = {idle, busy, done}
function st : node → node → phase
individual bad : Bool

#gen_state

after_init {
  st X Y := idle
  bad := false
}

action start (a b : node) {
  require st a b = idle ∧ a ≠ b
  st a b := busy
}

action finish (a b : node) {
  require st a b = busy
  st a b := done
}

action trip (a : node) {
  require st a a = done
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

/--
Certified: theorem EnumFun.ic3_safe (strengthening EnumFun.ic3_inv)
-/
#guard_msgs(info, substring := true) in
#updr (expect := invariant) certify

end EnumFun

veil module IntFun

type node
function cnt : node → node → Int
individual bad : Bool

#gen_state

after_init {
  cnt X Y := 0
  bad := false
}

action set (a b : node) {
  require a ≠ b
  cnt a b := 5
}

action trip (a : node) {
  require cnt a a = 5
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

/--
Certified: theorem IntFun.ic3_safe (strengthening IntFun.ic3_inv)
-/
#guard_msgs(info, substring := true) in
#updr (expect := invariant) certify

end IntFun

veil module IntFunBug

type node
function cnt : node → node → Int
individual bad : Bool

#gen_state

after_init {
  cnt X Y := if X = Y then 3 else -7
  bad := false
}

action trip (a b : node) {
  require cnt a b = -7 ∧ cnt b b = 3
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

/--
cnt: (0,0)↦3 (0,1)↦-7 (1,0)↦-7 (1,1)↦3
-/
#guard_msgs(info, substring := true) in
#updr (expect := unsafe) certify

end IntFunBug
