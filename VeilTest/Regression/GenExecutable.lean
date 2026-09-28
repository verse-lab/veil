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

#gen_spec

#gen_executable
#gen_executable

run_elab do
  unless (← Lean.getEnv).contains `GenExecutable.enumerableTransitionSystem do
    throwError "#gen_executable did not generate the executable transition system"

#model_check { node := Fin 2 } {}

end GenExecutable
