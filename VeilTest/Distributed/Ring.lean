module

public import Veil

/-! Leader election in a unidirectional ring (the protocol of
`Examples/Demo/Ring/RingDec.lean`), written as the program each node runs. -/

veil module DistRing

type node
instantiate tot : TotalOrder node
instantiate btwn : Between node
open Between TotalOrder

network (synchrony := async)

message token (id : node)

var leader : Bool := false

program (self : node) {
  let nxt :| ∀ z, self ≠ nxt ∧ ((z ≠ self ∧ z ≠ nxt) → btw self nxt z)
  send (token self) to nxt
  repeat
    recv (token id)
    if id = self then
      leader := true
    else if le self id then
      -- `nxt` was bound before the `recv`, so it is gone: find it again
      let nxt :| ∀ z, self ≠ nxt ∧ ((z ≠ self ∧ z ≠ nxt) → btw self nxt z)
      send (token id) to nxt
}

safety [single_leader] leader L1 ∧ leader L2 → L1 = L2
invariant [leader_greatest] leader L → le N L
invariant [receive_self_msg_only_if_greatest] token_net S L L → le N L
invariant [no_bypass] token_net P D S ∧ btw S N D → le N S

#gen_spec

#check_invariants

end DistRing
