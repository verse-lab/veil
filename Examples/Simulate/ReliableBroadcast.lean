import Veil

/-
Original source/reference:
- Local analogue: Examples/Ivy/ReliableBroadcast.lean
- External family reference: tlaplus/Examples/specifications/bcastByz/bcastByz.tla

Bug/race shape:
This simulate-focused variant keeps the initial/echo/vote/deliver structure, but
intentionally uses weak quorum rules. An equivocating originator can get two
different values delivered by different receivers.

Why #simulate here:
The violating trace is short, but exhaustive search must branch over broadcast,
echo, vote, and delivery orderings across many nodes and values.
-/

veil module ReliableBroadcastSim

type node
type value

immutable individual originator : node

relation initial_msg (src : node) (dst : node) (v : value)
relation echo_msg (src : node) (dst : node) (v : value)
relation vote_msg (src : node) (dst : node) (v : value)
relation delivered (dst : node) (v : value)

#gen_state

after_init {
  initial_msg S D V := false
  echo_msg S D V := false
  vote_msg S D V := false
  delivered D V := false
}

action initialSend (dst : node) (v : value) {
  require ∀ V, !(initial_msg originator dst V)
  initial_msg originator dst v := true
}

action echo (src : node) (v : value) {
  require initial_msg originator src v
  echo_msg src D v := true
}

action vote (observer : node) (v : value) {
  require ∃ (n1 n2 : node), n1 != n2 ∧ echo_msg n1 observer v ∧ echo_msg n2 observer v
  vote_msg observer D v := true
}

action deliver (observer : node) (v : value) {
  require ∃ (n1 n2 : node), n1 != n2 ∧ vote_msg n1 observer v ∧ vote_msg n2 observer v
  delivered observer v := true
}

safety [agreement]
  ∀ (n1 n2 : node) (v1 v2 : value), delivered n1 v1 ∧ delivered n2 v2 -> v1 = v2

#gen_spec

-- model_check must enumerate many broadcast, echo, vote, and delivery schedules.
-- set_option veil.violationIsError false in
-- #model_check { node := Fin 10, value := Fin 2 } { originator := (0 : Fin 10) }

-- simulate quickly finds an equivocation trace with the weak quorum rules above.
set_option veil.violationIsError false in
#simulate { node := Fin 10, value := Fin 2 } { originator := (0 : Fin 10) }
  (seed := 41) (maxTraces := 2000) (maxSteps := 24)

end ReliableBroadcastSim
