import Veil

veil module Unused

type node

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

#guard_msgs in
after_init {
  leader N := false
  pending M N := false
}

#guard_msgs in
action everyOneIsALeader {
  leader M := true
}

end Unused
