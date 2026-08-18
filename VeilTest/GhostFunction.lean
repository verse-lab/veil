import Veil

veil module GhostFunction

type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node → Bool
function rank : node → Nat
immutable function baseRank : node → Nat

#gen_state

after_init {
  leader N := false
  rank N := 0
}

-- Ghost relation (existing, backward compat)
ghost relation isLeader (n : node) := leader n

-- Ghost function with explicit return type annotation
ghost function getRank (n : node) : Nat := rank n

-- Ghost function without return type annotation (inferred)
ghost function doubleRank (n : node) := rank n + rank n

-- Theory ghost function
theory ghost function maxRank : Nat := 10
theory ghost function nextRank (r : Nat) := r + 1

action promote (n : node) {
  require ¬ isLeader n
  rank n := nextRank (baseRank n)
  leader n := true
}

safety [rank_nonneg] getRank N ≤ maxRank
safety [ghost_function_definitions]
  getRank N = rank N ∧
  doubleRank N = rank N + rank N ∧
  maxRank = 10 ∧
  nextRank (baseRank N) = baseRank N + 1

#gen_spec

/-- info: ✅ No violation (explored 32 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 5 } { baseRank := fun i => 2 * i }

end GhostFunction
