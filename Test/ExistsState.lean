import Veil.DSL

open Classical

section Test

type node

relation r (n : node) (m : node)
individual x : Prop

#gen_state Test

after_init {
  r N N := False
  x := False
}

action empty = {
  skip
}

/-- info: false -/
#guard_msgs in
#eval hasStateHOExist (Lean.mkConst `empty.tr.raw)


action call_empty = {
  call !empty
}

#print call_empty.tr.raw
/-- info: true -/
#guard_msgs in
#eval hasStateHOExist (Lean.mkConst `call_empty.tr.raw)

end Test
