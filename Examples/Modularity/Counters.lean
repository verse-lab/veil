module

public import Veil

set_option veil.smt.trust false
set_option veil.printCounterexamples false

veil module BoundedCounter

param limit : Nat
individual value : Nat
after_init { value := 0 }

action increment {
  require value < limit
  value := value + 1
  ensure old(value) ≤ value
}

invariant [bounded] value ≤ limit

#gen_spec
end BoundedCounter

veil module TwoCounters

isolate left : BoundedCounter (limit := 2)
isolate right : BoundedCounter (limit := 3)

safety [bounds] left.value ≤ 2 ∧ right.value ≤ 3

#gen_spec
#check_invariants left
#check_invariants
#gen_theorems

#check bounds.is_inv

end TwoCounters
