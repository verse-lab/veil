module

public import Veil

/-!
`#model_check (fingerprintType := T)` picks the type of the state fingerprints (default `Nat`).
The counterexample is recovered from the fingerprints in the search log, so it must come out the
same for `Nat` and `UInt64`, in both the parallel and the sequential search, and the other
configuration items must still apply.
-/

veil module FingerprintType

individual a : Bool
individual b : Bool
individual c : Bool

#gen_state

after_init {
  a := false
  b := false
  c := false
}

action step_a {
  require !a
  a := true
}

action step_b {
  require a
  b := true
}

action step_c {
  require b
  c := true
}

invariant [safe] ¬ c

#gen_spec

-- The default, `Nat`.
/--
error: ❌ Violation: safety_failure (violates: safe)
  State 0 (via init):
    a = false
    b = false
    c = false
  State 1 (via step_a):
    a = true
    b = false
    c = false
  State 2 (via step_b):
    a = true
    b = true
    c = false
  State 3 (via step_c):
    a = true
    b = true
    c = true
-/
#guard_msgs in
#model_check interpreted {} {}

-- `UInt64`, with the sequential search.
/--
error: ❌ Violation: safety_failure (violates: safe)
  State 0 (via init):
    a = false
    b = false
    c = false
  State 1 (via step_a):
    a = true
    b = false
    c = false
  State 2 (via step_b):
    a = true
    b = true
    c = false
  State 3 (via step_c):
    a = true
    b = true
    c = true
-/
#guard_msgs in
#model_check interpreted {} {} (fingerprintType := UInt64) (sequential := true)

-- An item before `fingerprintType` still applies: the depth bound stops the search before `step_c`.
/-- info: ✅ No violation (explored 3 states) -/
#guard_msgs in
#model_check interpreted {} {} (maxDepth := 1) (fingerprintType := UInt64)

-- A full ordinary configuration works before or after the fingerprint type. Later depth
-- settings still take precedence, whether supplied individually or through `config`.
/-- info: ✅ No violation (explored 3 states) -/
#guard_msgs in
#model_check interpreted {} {} (fingerprintType := UInt64) (maxDepth := 0)
  (config := { maxDepth := 1 })

/-- info: ✅ No violation (explored 3 states) -/
#guard_msgs in
#model_check interpreted {} {} (config := { maxDepth := 0 })
  (fingerprintType := UInt64) (maxDepth := 1)

end FingerprintType

/-!
A state with a single field hashes to that field's own hash, without `mixHash`; for an enum that
is the constructor's index (0, 1, 2 below). The default `Nat` fingerprint must keep the low bits:
shifting the hash right by one bit gave `a` and `b` the same fingerprint, and the search stopped
after 2 states.
-/

veil module FingerprintSingleField

enum E = {a, b, c}
individual x : E

#gen_state

after_init { x := a }
action step (i : E) { x := i }

invariant true

#gen_spec

/-- info: ✅ No violation (explored 3 states) -/
#guard_msgs in
#model_check interpreted {} {}

/-- info: ✅ No violation (explored 3 states) -/
#guard_msgs in
#model_check interpreted {} {} (fingerprintType := UInt64)

end FingerprintSingleField
