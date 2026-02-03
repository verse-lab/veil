import Veil
import VeilTest.TestUtil

set_option linter.unusedVariables false

veil module Test
type seq_t
type node
type block

individual x : Bool
individual b : block
relation r : block -> block -> Bool
function n_token_seq : node → seq_t
individual init_node : node

instantiate seq : TotalOrderWithMinimum seq_t

#gen_state

after_init {
  x := false;
  r b b := false
}

#guard_msgs in
action succ (n : seq_t) {
  let k : seq_t ← pick;
  require seq.next k n;
  return k
}

#guard_msgs in
action return_two (n : seq_t) {
  let m ← pick seq_t
  return (n, m)
}

#guard_msgs in
action pattern_bind (n : seq_t) {
  let (z, y) ← return_two n
  return z
}

#guard_msgs in
action create_one {
  let one ← succ seq.zero
  return one
}


#guard_msgs in
action capital_assign {
  let one : seq_t ← succ seq.zero
  n_token_seq N := if N = init_node then one else seq.zero
}

-- FIXME: we probably want to make this work!
#guard_msgs(drop error, drop warning) in
action call_in_capital_assign {
  n_token_seq N := if N = init_node then ← succ seq.zero else seq.zero
}

invariant true

#guard_msgs(drop error) in
#gen_spec
