import Veil

veil module GeneralizeFailing

type node
relation r (n : node) : Bool

after_init {
  pure ()
}

action act {
  let delivery ← pick (node → node → Bool)
  r N := decide $ (∃ sender, delivery sender N ∧ r sender)
}

invariant [inv] (∀ n₁ n₂, (r n₁ = r n₂))

#gen_spec

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  inv ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  act
    doesNotThrow ... ✅
    inv ... ❌
      Counterexample (WP):
        Theory:

        Pre-state:
          r = [0, 1]
        Action: act
      Counterexample (TR):
        Theory:

        Pre-state:
          r = [0, 1]
        Action: act
        Post-state:
          r = [0]
-/
#guard_msgs in
#check_invariants

end GeneralizeFailing
