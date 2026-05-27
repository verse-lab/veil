import Veil

veil module GenReachableInvariantsBase

type node

relation marked (N : node)

#gen_state

after_init {
  marked N := false
}

action Mark (n : node) {
  marked n := true
}

invset Trivial {
invariant [marked_self] marked N → marked N
}

#gen_spec

#check_invariants
#gen_theorems

end GenReachableInvariantsBase

veil module GenReachableInvariantsBase

#gen_reachable_invariants

#check Invariants.is_inv
#check marked_self.is_inv

end GenReachableInvariantsBase
