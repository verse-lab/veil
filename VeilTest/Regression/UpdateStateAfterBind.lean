import Veil

veil module UpdateStateAfterBind

type seq_t
instantiate seq : TotalOrderWithZero seq_t

immutable individual one : seq_t
individual x : seq_t
#gen_state

theory ghost relation lt (x y : seq_t) := (seq.le x y ∧ x ≠ y)
theory ghost relation next (x y : seq_t) := lt x y ∧ ∀ z, lt x z → seq.le y z

assumption [zero_one] next seq.zero one

procedure succ (n : seq_t) {
  let k ← pick seq_t
  assume next n k
  return k
}

after_init { x := seq.zero }

action does_not_actually_update_the_state {
  x ← succ x
}

#guard_msgs(drop warning) in
#gen_spec

sat trace {
  assert (x = seq.zero)
  does_not_actually_update_the_state
  assert (x = one)
}

end UpdateStateAfterBind
