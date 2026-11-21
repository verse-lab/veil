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
