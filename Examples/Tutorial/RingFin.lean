import Veil

veil module RingFin

type node

immutable function nextNode : node → node
immutable function le : node → node → Bool

individual leader : List node

@[veil_decl] structure Message (node : Type) where
  payload : node
  src : node
  dst : node

individual messages : List (Message node)

#gen_state

after_init {
  leader := []
  messages := []
}

procedure sendToNext (payload src : node) {
  let msg := Message.mk payload src (nextNode src)
  if msg ∉ messages then
    messages := msg :: messages
}

action send (n : node) {
  sendToNext n n
}

action recv {
  let m :| m ∈ messages
  let n := m.dst
  messages := messages.erase m
  if m.payload = n && n ∉ leader then
    leader := n :: leader
  else
    if le n m.payload then
      sendToNext m.payload n
}

safety [single_leader] leader.length ≤ 1
-- invariant [nodup_leader] leader.Nodup
-- invariant [nodup_messages] messages.Nodup

#gen_spec

-- #check_invariants

#model_check { node := Fin 4 }
{ nextNode := fun n => n + 1,
  le := fun n m => n < m }

end RingFin
