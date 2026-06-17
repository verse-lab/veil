import Veil

veil module PickNonEnumerableDiagnostic

relation available : Nat → Bool
individual picked : Nat

#gen_state

after_init {
  available N := false
  picked := 0
}

action choose_nat {
  let n : Nat :| available n = true
  picked := n
}

invariant picked = picked

#gen_spec

/--
error: could not extract executable choices for a nondeterministic pick.

A `let x :| p` choice must have finitely enumerable candidates. Provide a `Veil.Enumeration`/`MultiExtractor.Candidates` instance for the picked type, or use a finite/enumerated type instead of an infinite type such as `Nat`.
-/
#guard_msgs in
#model_check interpreted {}

end PickNonEnumerableDiagnostic
