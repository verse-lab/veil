import Mathlib.Data.List.Cycle
import Veil


veil module RingTheorems

immutable individual allNodes : List Nat

individual leader : List Nat

@[veil_decl] structure Message where
  payload : Nat
  src : Nat
  dst : Nat

individual messages : List Message

#gen_state

theory ghost function nextNode (n : Nat) : Nat :=
  if h : n ∈ allNodes then allNodes.next n h else n

theory ghost relation lt (x y : Nat) := allNodes.idxOf x ≤ allNodes.idxOf y ∧ x ≠ y

theory ghost relation btw (x y z : Nat) :=
  (lt x y ∧ lt y z) ∨ (lt z x ∧ lt x y) ∨ (lt y z ∧ lt z x)

theory ghost relation isNext (n : Nat) (next : Nat) :=
  n ∈ allNodes ∧ next ∈ allNodes ∧ n ≠ next ∧
  ∀ Z ∈ allNodes, Z ≠ n ∧ Z ≠ next → btw n next Z

assumption [allNodes_nodup] allNodes.Nodup
assumption [allNodes_nontrivial] 1 < allNodes.length

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

#gen_spec

#check_invariants

end RingTheorems
