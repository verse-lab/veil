module

public import Veil

veil module PickNonEnumerableDiagnostic

relation available : Nat → Bool
individual picked : Nat

/--
warning: Field `available` uses a hybrid representation. Updates over potentially unbounded domains (e.g. `f I := ...`) can switch it to the canonical case, where default `Hashable` or `BEq` instances can merge distinct states and miss reachable states during model checking. For meaningful hashing and equality in the canonical case, define higher-priority instances for `Veil.CanonicalFieldWrapper` before state generation; see `docs/DSL-Reference.md#hybrid-field-representations`. If the field stays concrete, suppress this warning with `set_option veil.warnHybridFields false`. Alternatively, consider `TMap` if it better fits your model.
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
