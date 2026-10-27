module

public import Veil

attribute [instance] leOfOrd

veil module RingNat

immutable individual allNodes : List Nat
immutable function nextNode : Nat → Nat

individual leader : List Nat

@[veil_decl] structure Message where
  payload : Nat
  src : Nat
  dst : Nat

individual messages : List Message

#gen_state

after_init {
  leader := []
  messages := []
}

procedure sendToNext (payload src : Nat) {
  let msg := Message.mk payload src (nextNode src)
  if msg ∉ messages then
    messages := messages.insertOrdered msg
}

action send {
  let n :| n ∈ allNodes
  sendToNext n n
}

action recv {
  let m :| m ∈ messages
  let n := m.dst
  messages := messages.erase m
  if m.payload = n && n ∉ leader then
    leader := n :: leader
  else
    if n ≤ m.payload then
      sendToNext m.payload n
}

safety [single_leader] leader.length ≤ 1
invariant [messages_nodup] messages.Nodup

#gen_spec

-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s. There are
-- none, hence `{ }`: the nodes are natural numbers.
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields:
-- * `allNodes := [1, 2, 3, 4, 5]`: the nodes.
-- * `nextNode := fun n => match n with ...`: each node's successor on the ring
--   `1 → 5 → 2 → 4 → 3 → 1`.
#model_check { }
  { allNodes := [1, 2, 3, 4, 5],
    nextNode := fun n =>
        match n with
        | 1 => 5
        | 5 => 2
        | 2 => 4
        | 4 => 3
        | 3 => 1
        | _ => 0    -- we don't care about anything outside `allNodes`
   }

end RingNat
