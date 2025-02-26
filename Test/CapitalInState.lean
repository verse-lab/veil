import Veil.DSL
import Test.TestUtil


set_option linter.unusedVariables false

veil module Test
type seq_t
type node
type block

individual x : Prop
individual b : block
relation r : block -> block -> Prop
function n_RR : node → seq_t
function n_RN : node → node → seq_t
individual X : Prop

#gen_state

after_init { pure () }

#guard_msgs in
action set_n_RR (n : node) (s : seq_t) = {
  n_RR n := s
}

#guard_msgs in
action set_n_RN (n m : node) (s : seq_t) = {
  n_RN n m := s
}

#guard_msgs in
action set_n_RN_capital (n m : node) (s : seq_t) = {
  n_RN N m := s
}

#guard_msgs in
action set_X = {
  X := True
}
