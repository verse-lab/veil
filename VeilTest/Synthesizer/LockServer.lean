module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! A lock server whose mutual exclusion needs one strengthening clause: the
command finds it. -/

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
#synthesize_invariants

end LockServer
