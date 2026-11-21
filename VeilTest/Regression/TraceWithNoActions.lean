module

public import Veil

veil module TraceWithNoActions

type node
type value

immutable individual v₀ : value
relation W (n : node) (v : value) : Bool

after_init {
  W N V := V == v₀
}

#guard_msgs(drop warning) in
#gen_spec

-- We are testing that there is no error here
#guard_msgs(drop info) in
sat trace {}

end TraceWithNoActions

veil module TraceWithUnusedQuantifier

type node
individual flag : Bool

after_init { flag := false }

#guard_msgs(drop warning) in
#gen_spec

/--
info: ✅ Satisfying trace found
  Instantiation:
    node = Fin 1
  State 0 (via init):
    flag = false
-/
#guard_msgs in
set_option veil.smt.trust true in
sat trace {
  assert (∀ _x : node, flag = false)
}

end TraceWithUnusedQuantifier
