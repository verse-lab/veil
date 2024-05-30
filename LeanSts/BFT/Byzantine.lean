import Mathlib.Tactic

#check Finset

/-- A Byzantine setting in which the Byzantine nodes are fixed ahead of time. -/
class NonadaptiveByzantineSetting {NetAddr : Type} :=
  /-- Total number of nodes. -/
  N : ℕ
  /-- Number of permitted Byzantine faults. -/
  f : ℕ
  /-- Is this node Byzantine? -/
  isByzantine : NetAddr → Bool

  N_gt_0 : 0 < N
  f_lt_N : f < N
  -- byz_lte_f :
  --   {n | isByzantine n = true} ≤ f


/-- A Byzantine adversary is constrained in terms of the messages it can produce
  in a given NetworkState (which can include history information). -/
class AdversaryConstraint {Message NetworkState : Type} :=
  canProduceMessage : Message → NetworkState  → Prop

class ByzantineAdversary {NetAddr Message NetworkState : Type} :=
  setting : @NonadaptiveByzantineSetting NetAddr
  constraint : @AdversaryConstraint Message NetworkState
