module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! Counterexamples whose labels carry several arguments of different sorts: nodes, enum
constructors and `Bool`. `certify` rebuilds each label from the model's transition labels. -/

veil module MixedLabels

type node
enum phase = {idle, busy, done}
relation at_ : node → phase → Bool
individual flag : Bool
individual bad : Bool

#gen_state

after_init {
  at_ N P := P == idle
  flag := false
  bad := false
}

action move (n : node) (p q : phase) (b : Bool) {
  require at_ n p ∧ p ≠ q
  at_ n p := false
  at_ n q := true
  flag := b
}

action trip (n m : node) (p : phase) {
  require at_ n p ∧ at_ m done ∧ n ≠ m ∧ p = busy ∧ flag
  bad := true
}

safety [never_bad] ¬ bad

#gen_spec

/--
step: {"trip": {"p": "busy", "n": 0, "m": 1}}
-/
#guard_msgs(info, substring := true) in
#synthesize_invariants (expect := unsafe) certify

end MixedLabels
