module

public import Veil

/-! The lock server of `LockServer.lean`, with declared invariants. The command
includes them in the property unless `(invariants := false)`, and names the
clauses it suggests `ic3_k` with indices whose names are not already taken. -/

veil module DeclaredInvariants

type client

relation waiting : client → Bool
relation holds : client → Bool
individual lock_free : Bool

#gen_state

after_init {
  waiting C := false
  holds C := false
  lock_free := true
}

action request (c : client) {
  waiting c := true
}

action grant (c : client) {
  require lock_free
  require waiting c
  waiting c := false
  holds c := true
  lock_free := false
}

action release (c : client) {
  require holds c
  holds c := false
  lock_free := true
}

safety [mutex] holds C ∧ holds D → C = D
invariant [lock_held] holds C → ¬ lock_free

#gen_spec

/-- the property is inductive on its own -/
#guard_msgs(info, substring := true) in
#updr (expect := invariant)

/-- invariant [ic3_0] ∀ (x0 : client), ¬ holds x0 ∨ ¬ lock_free -/
#guard_msgs(info, substring := true) in
#updr (invariants := false) (expect := invariant)

end DeclaredInvariants

veil module TakenNames

type client

relation waiting : client → Bool
relation holds : client → Bool
individual lock_free : Bool

#gen_state

after_init {
  waiting C := false
  holds C := false
  lock_free := true
}

action request (c : client) {
  waiting c := true
}

action grant (c : client) {
  require lock_free
  require waiting c
  waiting c := false
  holds c := true
  lock_free := false
}

action release (c : client) {
  require holds c
  holds c := false
  lock_free := true
}

safety [mutex] holds C ∧ holds D → C = D
invariant [ic3_0] holds C → holds C

#gen_spec

/--
Insert the strengthening invariants before #gen_spec:

  [apply] invariant [ic3_1] ∀ (x0 : client), ¬ holds x0 ∨ ¬ lock_free
-/
#guard_msgs(info, substring := true) in
#updr (expect := invariant)

end TakenNames
