import Veil

veil module GhostIndividual

enum Phase = {idle, active}

individual phase : Phase

#gen_state

-- State ghost individuals, with an explicit and an inferred result type.
ghost individual phaseSnapshot : Phase := phase
ghost individual inferredPhase := phase

-- Theory ghost individuals, with an explicit and an inferred result type.
theory ghost individual initialPhase : Phase := idle
theory ghost individual inferredInitialPhase := idle

after_init {
  phase := initialPhase
}

action toggle {
  if phaseSnapshot = idle then
    phase := active
  else
    phase := idle
}

safety [ghost_individual_definitions]
  phaseSnapshot = phase ∧
  inferredPhase = phase ∧
  initialPhase = idle ∧
  inferredInitialPhase = idle

#gen_spec

/-- info: ✅ No violation (explored 2 states) -/
#guard_msgs in
#model_check { } { }

#guard_msgs(drop info) in
#check_invariants

end GhostIndividual
