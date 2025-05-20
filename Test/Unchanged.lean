import Veil

veil module Foo

individual foobar : Bool

#gen_state

after_init { foobar := true }

#guard_msgs(drop warning) in
#gen_spec

end Foo

veil module List

type elt

individual foobar : Bool

includes Foo

individual contents : List elt

#gen_state

action clear = {
  contents := []
}

after_init { clear }

input action enqueue (e : elt) = {
  contents := contents ++ [e]
}

input action dequeue = {
  let res := contents.head?
  contents := contents.tail
  return res
}

#guard_msgs(drop warning) in
#gen_spec

end List


inductive removed (x : A) : List A → List A → Prop
| removed_here : forall xs, removed x (x :: xs) xs
| removed_inside : forall y xs ys, removed x xs ys -> removed x (y :: xs) (y :: ys)


veil module ReliableReorderingChannel
type msg

includes List msg _ _ as l

#gen_state

after_init { l.clear }

input action send (m : msg) = { l.enqueue m }

input transition recv (m : msg) = { removed m l.contents l'.contents }

-- The point of this test is to check that `unchanged` recursively descends into
-- the modules included in the state.

/--
info: def ReliableReorderingChannel.recv.tr : {msg : Type} →
  [msg_dec : DecidableEq msg] → [msg_ne : Nonempty msg] → State msg → State msg → Prop :=
fun {msg} [DecidableEq msg] [Nonempty msg] =>
  let t := fun st st' =>
    ∃ m, (st.l.foobar = st'.l.foobar ∧ st.l.Foo.foobar = st'.l.Foo.foobar) ∧ removed m st.l.contents st'.l.contents;
  t
-/
#guard_msgs in
#print recv.tr

#guard_msgs(drop warning) in
#gen_spec

end ReliableReorderingChannel
