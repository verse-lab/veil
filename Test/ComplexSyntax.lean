import Veil.DSL
import Veil.TestUtil
import Examples.DSL.Std

open Classical
set_option linter.unusedVariables false

section Test
type seq_t
type node
type block

individual x : Prop
individual b : block
relation r : block -> block -> Prop
function n_token_seq : node → seq_t

instantiate seq : TotalOrderWithMinimum seq_t

#gen_state Test

after_init {
  x := False;
  r b b := False
}

#guard_msgs in
action succ (n : seq_t) = {
  let k : seq_t ← fresh;
  require seq.next k n;
  return k
}

#guard_msgs in
action return_two (n : seq_t) = {
  let m ← fresh seq_t
  return (n, m)
}

#guard_msgs in
action pattern_bind (n : seq_t) = {
  let (x, y) ← return_two n
  return x
}

#guard_msgs in
action create_one = {
  let one ← succ seq.zero
  return one
}

-- FIXME Vova: this is a BROKEN test
#guard_msgs(drop error, drop warning) in
action capital_assign = {
  let one : seq_t ← succ seq.zero
  n_token_seq N := if N = init_node then one else seq.zero;

}

-- set_option trace.dsl.debug true
-- FIXME Vova: this is a BROKEN test
#guard_msgs(drop error, drop warning) in
action call_in_capital_assign = {
  n_token_seq N := if N = init_node then ← succ seq.zero else seq.zero;
}

invariant True

#gen_spec Test
