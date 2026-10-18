module

public import Veil

/-!
Dependent action arguments must be specialized with earlier supplied values,
without capturing equally named trace bindings. These manual trace proofs test
elaboration independently of the SMT backend's support for dependent types.
-/

veil module TraceBindingsDependent

individual observed : Nat

#gen_state

after_init { observed := 0 }

action record (n : Fin 3) (m : Fin 3) (x : Fin (m.val + 1)) {
  observed := n.val + m.val + x.val
}

invariant true

#gen_spec

-- The header's `n` in the second argument must not be captured by the
-- action's first parameter, whose supplied value is zero.
unsat trace [dependent_supplied] (n : Fin 3) (_impossible : False) {
  record 0 n (⟨n.val, Nat.lt_succ_self n.val⟩)
} by
  intros
  contradiction

-- Header binders also form a telescope, and the final argument's type is
-- specialized to the actual second argument rather than its witness observer.
unsat trace [dependent_header] (n : Fin 3) (x : Fin (n.val + 1)) (_impossible : False) {
  record 0 n x
} by
  intros
  contradiction

-- A wildcard can have a type depending on an earlier pre-state expression.
unsat trace [dependent_prestate] (_impossible : False) {
  record 0 ((if observed = 0 then 0 else 1) : Fin 3) _
} by
  intros
  contradiction

-- Bare action names still create a correctly scoped dependent telescope.
unsat trace [dependent_bare] (_impossible : False) {
  record
} by
  intros
  contradiction

end TraceBindingsDependent
