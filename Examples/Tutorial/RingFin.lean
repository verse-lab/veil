import Veil

veil module RingFin

type node
-- This allows us to use the `≤` notation
instantiate inst : LE node
instantiate decLE : DecidableRel inst.le
-- This allows us to insert into the messages list in order
instantiate ord : Ord node

immutable function nextNode : node → node

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
    messages := messages.insertOrdered msg
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
    if n ≤ m.payload then
      sendToNext m.payload n
}

safety [single_leader] leader.length ≤ 1
invariant [messages_nodup] messages.Nodup

#gen_spec

#model_check { node := Fin 4 } { nextNode := fun n => n + 1 }

end RingFin
