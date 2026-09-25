module

public import Mathlib.Data.List.Cycle
public import Veil

public section


veil module RingConc

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
invariant [leader_wf] ∀ L ∈ leader, L ∈ allNodes
invariant [msg_wf] ∀ m ∈ messages, m.payload ∈ allNodes ∧ m.src ∈ allNodes ∧ m.dst ∈ allNodes
invariant [leader_greatest] ∀ L ∈ leader, ∀ N ∈ allNodes, N ≤ L
invariant [self_msg_greatest] ∀ m ∈ messages, m.payload = m.dst → ∀ N ∈ allNodes, N ≤ m.payload
invariant [drop_smaller] ∀ m ∈ messages, ∀ N ∈ allNodes, btw m.payload N m.dst → N ≤ m.payload


set_option veil.solver "grind+smt"
set_option veil.smt.trust false
#gen_spec

/-! The concrete safety property is proved by CSLib simulation in `RingRef.lean`.
The direct concrete VC proofs from the dissertation are not needed for that proof. -/

end RingConc
