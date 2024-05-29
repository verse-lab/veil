import Mathlib.Tactic

class ByzantineThreshold :=
  /-- Total number of nodes. -/
  N : ℕ
  /-- Number of permitted Byzantine faults. -/
  f : ℕ

  N_gt_0 : 0 < N
  f_lt_N : f < N

instance ClassicByzantineThreshold (N : ℕ) (N_gt_0 : 0 < N) : ByzantineThreshold :=
  ⟨N, ⌊N / 3⌋₊, N_gt_0, by simp ; omega⟩

/-- A Byzantine setting in which the Byzantine nodes are fixed ahead of time. -/
class NonadaptiveByzantineSetting {NetAddr : Type} :=
  /-- Is this node Byzantine? -/
  isByzantine : NetAddr → Bool

/-- A Byzantine setting in which the Byzantine nodes potentially vary over time. -/
class ByzantineSetting {NetAddr NetworkState : Type} :=
  /-- Is this node Byzantine? -/
  isByzantine : NetAddr → NetworkState → Bool

/-- A non-adaptive Byzantine setting is a restricted form of the adaptive setting. -/
instance [na : @NonadaptiveByzantineSetting NetAddr] : @ByzantineSetting NetAddr NetworkState :=
  ⟨λ addr _ => na.isByzantine addr⟩

/-- A Byzantine adversary is constrained in terms of the messages it can produce
  in a given NetworkState (which can include history information). -/
class AdversaryConstraint {Message NetworkState : Type} :=
  canProduceMessage : Message → NetworkState  → Prop

class ByzantineAdversary {NetAddr Message NetworkState : Type} :=
  setting : @ByzantineSetting NetAddr NetworkState
  constraint : @AdversaryConstraint Message NetworkState
