import Veil

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

-- #check_invariants

end RingNat
