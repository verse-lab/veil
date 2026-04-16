import Veil

set_option linter.unusedVariables false

veil module TestParameter

type node
param n : Nat
type color
param m : Fin (n + 1)

function counter : node → Nat
relation palette : node → color → Fin (n + 1) → Bool

#gen_state

after_init {
  counter N := 0
  palette N C I := false
}

action increment (x : node) {
  require counter x < n
  counter x := counter x + 1
}

action paint (x : node) (c : color) {
  palette x c m := true
}

invariant [bounded] ∀ (x : node), counter x ≤ n

#gen_spec

#model_check interpreted { node := Fin 2, n := 1, color := Fin 2, m := ⟨1, by decide⟩ } {}

#guard_msgs(drop info) in
#simulate interpreted { node := Fin 2, n := 1, color := Fin 2, m := ⟨1, by decide⟩ } {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

end TestParameter
