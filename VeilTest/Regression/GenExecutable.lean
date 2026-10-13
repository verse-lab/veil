module

public import Veil

veil module GenExecutable

type node
relation marked (n : node)

#gen_state

after_init {
  marked N := false
}

action mark {
  let n : node ← pick
  marked n := true
}

invariant true

#gen_spec

#gen_executable
#gen_executable

run_elab do
  unless (← Lean.getEnv).contains `GenExecutable.enumerableTransitionSystem do
    throwError "#gen_executable did not generate the executable transition system"

#model_check { node := Fin 2 } {}

end GenExecutable

-- `-borrowArgs` extracts the actions owned; `#model_check` then uses those definitions.
veil module GenExecutableOwned

type node
relation marked (n : node)

#gen_state

after_init {
  marked N := false
}

action mark {
  let n : node ← pick
  marked n := true
}

invariant true

#gen_spec

#gen_executable -borrowArgs

#model_check { node := Fin 2 } {}

end GenExecutableOwned
