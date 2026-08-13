import Veil


veil module foo_mod

relation foo : BitVec 1 → BitVec 1 → Bool

after_init {
  foo R C := false
  foo 0 1 := true

}

invariant ¬ (foo 0 0)
invariant ¬ (foo 0 1)

invariant ¬ (foo 0 0 ∧ foo 0 1)

#time
/-- warning: you have not defined any actions for this specification; did you forget? -/
#guard_msgs in
#gen_spec

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  inv_0 ... ✅
  inv_1 ... ❌
      Counterexample (WP):
        Theory:

        Pre-state:
          foo = []
        Action: initializer
      Counterexample (TR):
        Theory:

        Pre-state:
          foo = []
        Action: initializer
        Post-state:
          foo = [[0x0#1, 0x1#1]]
  inv_2 ... ✅
-/
#guard_msgs in
#check_invariants

end foo_mod
