module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! The lock server with a bug: `grant` does not check that the lock is free.
The command finds an execution in which two clients hold the lock and
certifies it as `LockServerBug.ic3_unsafe`. -/

veil module LockServerBug

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

#gen_spec

/-- info: Violated: the safety property. Execution of 4 step(s) -/
#guard_msgs(info, substring := true) in
#updr (expect := unsafe) certify

#gen_theorems

/-- info: 'LockServerBug.ic3_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LockServerBug.ic3_unsafe

end LockServerBug
