module

public import Veil

veil module PickNonEnumerableDiagnostic

relation available : Nat → Bool
individual picked : Nat

/--
warning: Field `available` uses a hybrid representation with default canonical `Hashable` or `BEq` instances, which can cause model checking to merge distinct states and miss reachable states. For meaningful hashing and equality, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation.
-/
#guard_msgs in
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
