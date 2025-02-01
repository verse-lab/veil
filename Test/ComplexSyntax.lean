import Veil.DSL
import Veil.TestUtil
import Library.Std

open Classical
set_option linter.unusedVariables false

namespace Test
type seq_t
type node
type block

individual x : Prop
individual b : block
relation r : block -> block -> Prop
function n_token_seq : node → seq_t
individual init_node : node

instantiate seq : TotalOrderWithMinimum seq_t

#gen_state

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
  let (z, y) ← return_two n
  return z
}

#guard_msgs in
action create_one = {
  let one ← succ seq.zero
  return one
}


#guard_msgs in
action capital_assign = {
  let one : seq_t ← succ seq.zero
  -- FIXME: This line works, but it screws up the highlighting of the whole file
  n_token_seq N := if N = init_node then one else seq.zero

}

/-
  Vova: not sure how to fix this.
  In the theory we can have
  ```x N := (<- foo N)```
  which expands to
  ```x := fun N => (<- foo N)```
  But we cannot lift `foo` under the lambda.
  `fun N => (<- foo N)` is equivalent to `foo`, which is a monadic computation. Whereas `x` is simple function.

-/
#guard_msgs(drop error, drop warning) in
action call_in_capital_assign = {
  n_token_seq N := if N = init_node then ← succ seq.zero else seq.zero
}

invariant True

#gen_spec
