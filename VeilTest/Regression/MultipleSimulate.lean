import Veil

veil module MultipleSimulate

type node

relation flag : node -> Bool

after_init {
  flag N := false
}

action set_flag (n : node) {
  flag n := true
}

invariant [bounded] ∀ n, flag n -> flag n

#guard_msgs(drop warning) in
#gen_spec

#guard_msgs(drop info) in
#simulate interpreted { node := Fin 2 } {} (seed := 1) (maxTraces := 1) (maxSteps := 1)

#guard_msgs(drop info) in
#simulate interpreted { node := Fin 2 } {} (seed := 2) (maxTraces := 1) (maxSteps := 1)

end MultipleSimulate
