module

public import Veil

veil module DistributedGhostBinderShadowing

type node
network (synchrony := async)
var n : Bool := false

program (self : node) {
  n := true
}

-- The generated `halted` ghost takes a node argument even when there is a node variable named `n`.
invariant [haltedSetN] ∀ i : node, halted i → n i

#gen_spec

end DistributedGhostBinderShadowing

veil module DistributedReceivedBinder

type node
network (synchrony := sync)
message offer (n : node)
var seen : Bool := false

program (self : node) {
  broadcast (offer self)
  next_round
  let net_src := self
  seen := decide (received (offer net_src))
}

invariant True
#gen_spec

end DistributedReceivedBinder
