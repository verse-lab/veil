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

/-- error: don't know how to synthesize placeholder -/
#guard_msgs (substring := true) in
#model_check interpreted { node := _ } {}

/-- error: don't know how to synthesize placeholder -/
#guard_msgs (substring := true) in
#model_check compiled { node := _ } {}

run_elab do
  unless (← Lean.getEnv).contains `GenExecutable.enumerableTransitionSystem do
    throwError "#gen_executable did not generate the executable transition system"

#model_check { node := Fin 2 } {}

@[default_instance] instance inferredNode : Enumeration (Fin 2) := inferInstance

#model_check interpreted { node := _ } {}
#model_check compiled { node := _ } {}

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
