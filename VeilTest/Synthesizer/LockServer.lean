module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! A lock server whose mutual exclusion needs one strengthening clause: the
command finds it and certifies it as `LockServer.ic3_safe`, a theorem on the
standard axioms. -/

veil module LockServer

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

#gen_spec

/-- invariant [ic3_0] ∀ (x0 : client), ¬ holds x0 ∨ ¬ lock_free -/
#guard_msgs(info, substring := true) in
#synthesize_invariants certify

#gen_theorems

/-- info: 'LockServer.ic3_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LockServer.ic3_safe

end LockServer
