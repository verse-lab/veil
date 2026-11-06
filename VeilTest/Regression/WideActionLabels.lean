module

public import Veil

/-! A module with 24 one-parameter actions. `#gen_spec` derives `FinEncodableInjOnly` for
its action labels, one constructor per action. The derivation's proof used to take time
exponential in the number of such constructors, and ran out of heartbeats at 24. -/

veil module WideActionLabels

type node
relation r (n : node) : Bool

#gen_state

after_init { r N := false }

action a0 (n : node) { r n := true }
action a1 (n : node) { r n := true }
action a2 (n : node) { r n := true }
action a3 (n : node) { r n := true }
action a4 (n : node) { r n := true }
action a5 (n : node) { r n := true }
action a6 (n : node) { r n := true }
action a7 (n : node) { r n := true }
action a8 (n : node) { r n := true }
action a9 (n : node) { r n := true }
action a10 (n : node) { r n := true }
action a11 (n : node) { r n := true }
action a12 (n : node) { r n := true }
action a13 (n : node) { r n := true }
action a14 (n : node) { r n := true }
action a15 (n : node) { r n := true }
action a16 (n : node) { r n := true }
action a17 (n : node) { r n := true }
action a18 (n : node) { r n := true }
action a19 (n : node) { r n := true }
action a20 (n : node) { r n := true }
action a21 (n : node) { r n := true }
action a22 (n : node) { r n := true }
action a23 (n : node) { r n := true }

invariant [trivial] True

#guard_msgs in
#gen_spec

end WideActionLabels
