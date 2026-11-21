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
relation x0 : client → Bool
individual lock_free : Bool

#gen_state

after_init {
  waiting C := false
  x0 C := false
  lock_free := true
}

action request (c : client) {
  waiting c := true
}

action grant (c : client) {
  require lock_free
  require waiting c
  waiting c := false
  x0 c := true
  lock_free := false
}

action release (c : client) {
  require x0 c
  x0 c := false
  lock_free := true
}

safety [mutex] x0 C ∧ x0 D → C = D
invariant [ic3_0] x0 C → x0 C

#gen_spec

/--
Insert the strengthening invariants before #gen_spec:

  [apply] invariant [ic3_1] ∀ (x0' : client), ¬ x0 x0' ∨ ¬ lock_free
-/
#guard_msgs(info, substring := true) in
#updr (expect := invariant) certify

end TakenNames

veil module QueryBinderShadowing

individual ActionTag : Bool
individual th : Bool
individual st0 : Bool
individual st1 : Bool
individual _tr1_tag : Bool
individual _tr1_act_keep_arg0_value : Bool

#gen_state

after_init {
  ActionTag := false
  th := false
  st0 := false
  st1 := false
  _tr1_tag := false
  _tr1_act_keep_arg0_value := false
}

action keep (value : Bool) {
  require value
}

safety [neverSet] ¬ ActionTag ∧ ¬ th ∧ ¬ st0 ∧ ¬ st1 ∧ ¬ _tr1_tag ∧ ¬ _tr1_act_keep_arg0_value

#gen_spec

/-- Certified: theorem QueryBinderShadowing.ic3_safe -/
#guard_msgs (info, substring := true) in
#updr (expect := invariant) certify

end QueryBinderShadowing

veil module NormalizationBinderShadowing

type st0
relation seen : st0 → Bool

after_init { seen X := false }
action keep { pure () }
safety [clean] ∀ x : st0, ¬ seen x

#gen_spec

/-- transition relation normalized once -/
#guard_msgs (substring := true) in
#updr (expect := invariant)

end NormalizationBinderShadowing

veil module SameNamedTheoryAndState

immutable individual shared : Bool
/-- warning: mutable state component `shared` shadows immutable theory component `shared`; references to this name resolve to the state component -/
#guard_msgs in
individual shared : Bool

assumption shared = true
after_init { shared := false }
action idle { pure () }
safety [prop] shared = true

#gen_spec

/-- error: IC3: theory and state both declare `shared`. Rename one before running #updr. -/
#guard_msgs in
#updr (expect := unsafe) certify

end SameNamedTheoryAndState
