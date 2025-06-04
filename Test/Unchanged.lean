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

includes Foo as F

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

input transition recv (m : msg) = { True }

-- The point of this test is to check that `unchanged` recursively descends into
-- the modules included in the state.

/--
info: def ReliableReorderingChannel.recv.tr : {msg : Type} →
  [msg_dec : DecidableEq msg] →
    [msg_ne : Nonempty msg] → {σ : Type} → [σ_substate : IsSubStateOf (State msg) σ] → σ → σ → Prop :=
fun {msg} [DecidableEq msg] [Nonempty msg] {σ} [IsSubStateOf (State msg) σ] =>
  let t := fun st st' =>
    ∃ m,
      ((getFrom st).l.foobar = (getFrom st').l.foobar ∧
          (getFrom st).l.F.foobar = (getFrom st').l.F.foobar ∧ (getFrom st).l.contents = (getFrom st').l.contents) ∧
        True;
  t
-/
#guard_msgs in
#print recv.tr

#guard_msgs(drop warning) in
#gen_spec

end ReliableReorderingChannel
