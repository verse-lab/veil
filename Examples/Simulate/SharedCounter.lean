import Veil

/-
Demonstrates #simulate advantage over #model_check on large state spaces.

N processes each have a boolean active flag, creating 2^N flag combinations.
A shared counter increments when any active process acts. Safety: counter < 10.

With Fin 20 (20 processes), the state space is ~2^20 * 10 ~ 10M states --
intractable for exhaustive model checking. Simulate finds the violation in a
single trace by activating one process and incrementing 10 times.
-/
veil module SharedCounter

type process

individual counter : Nat
relation active : process -> Bool

#gen_state

after_init {
  counter := 0
  active P := false
}

action activate (p : process) {
  require ¬ active p
  active p := true
}

action deactivate (p : process) {
  require active p
  active p := false
}

action increment (p : process) {
  require active p
  counter := counter + 1
}

safety [bounded] counter < 10

#gen_spec

-- model_check needs to explore ~10M states (times out even after 60s)
-- set_option veil.violationIsError false in
-- #model_check { process := Fin 20 } {}

-- simulate finds the violation in a single trace
set_option veil.violationIsError false in
#simulate { process := Fin 20 } {} (maxTraces := 100) (maxSteps := 50)

end SharedCounter
