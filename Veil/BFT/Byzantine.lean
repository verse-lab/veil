import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-- `N` number of nodes, with at most `f` faults. -/
class ByzantineSetting {NetAddr : Type} :=
  /-- Set of all nodes. -/
  nodes : Finset NetAddr
  /-- Total number of nodes. -/
  N : ℕ
  /-- Number of permitted Byzantine faults. -/
  f : ℕ

  N_nodes : nodes.card = N
  N_gt_0 : 0 < N
  f_lt_N : f < N

/-- A Byzantine adversary is constrained in terms of the messages it can produce
  in a given NetworkState (which can include history information). -/
class AdversaryConstraint {Packet NetworkState : Type} :=
  canProducePacket : Packet → NetworkState  → Prop

/-- A Byzantine adversary which chooses ahead-of-time which nodes
    are corrupted, i.e. a non-adaptive adversary. -/
class NonadaptiveByzantineAdversary {NetAddr Packet NetworkState : Type} :=
  setting : @ByzantineSetting NetAddr
  constraint : @AdversaryConstraint Packet NetworkState

  /-- Is this node corrupted? -/
  isByzantine : NetAddr → Bool
  /-- The `isByzantine` function respects the threshold `f` -/
  byz_lte_f : (setting.nodes.filter (isByzantine ·)).card ≤ setting.f
