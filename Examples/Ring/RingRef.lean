import Examples.Ring.RingConc
import Examples.Ring.RingAbs

/-!
# Refinement proof that `RingConc` satisfies `single_leader`

`RingConc.lean` (module `RingTheorems`) is a *concrete* ring–leader–election
specification over `Nat` node identifiers, with a `List Nat` leader register and
a `List Message` message pool.  Its safety property `single_leader` states that
at most one leader is ever elected: `leader.length ≤ 1`.

`RingAbs.lean` (module `RingDec`) is the *abstract* version of the same protocol,
over an abstract `node` type equipped with a `TotalOrder` and a `Between` (ring)
structure, using relational state `leader : node → Bool`, `pending : node → node →
Bool`.  For the abstract version the inductive invariant — and therefore the
abstract safety property `single_leader` — is already discharged (see
`RingDec.single_leader.is_inv`).

This file connects the two with a `PointedForwardSimulation` (from
`Veil/Core/Tools/ModelChecker/TransitionSystem.lean`) and transports the abstract
safety property back to the concrete system, *without modifying `RingConc.lean`*.

The abstract `node` type is instantiated, for a fixed concrete background theory
`allNodes = L`, with the subtype `{x : ℕ // x ∈ L}`:

* the abstract `TotalOrder` orders nodes by their underlying `Nat` value — this
  matches the concrete comparison `n ≤ m.payload`;
* the abstract `Between` (ring topology) orders nodes by their *position* in `L`
  via `L.idxOf` — this matches the concrete successor function `nextNode = L.next`.

These two orders are independent, exactly as `TotalOrder` and `Between` are
independent type classes in `RingAbs`.

-/

open Veil RelationalTransitionSystem

namespace RingRef

/-! ## Characterizations of the concrete transition system -/

/-- Abbreviation for the concrete (`RingTheorems`) transition system. -/
noncomputable abbrev CC : RelationalTransitionSystem RingTheorems.Theory
    (RingTheorems.State RingTheorems.FieldAbstractType) RingTheorems.Label :=
  RingTheorems.relationalTransitionSystem

theorem cc_assumptions (th : RingTheorems.Theory) :
    CC.assumptions th ↔ th.allNodes.Nodup ∧ 1 < th.allNodes.length := by
  simp only [CC, RingTheorems.relationalTransitionSystem, invSimp, RingTheorems.Assumptions]

theorem cc_init (th : RingTheorems.Theory) (s : RingTheorems.State RingTheorems.FieldAbstractType) :
    CC.init th s ↔ (⟨[], []⟩ : RingTheorems.State RingTheorems.FieldAbstractType) = s := by
  simp only [CC, RingTheorems.relationalTransitionSystem, nextSimp, RingTheorems.Init,
    RingTheorems.instAbstractFieldRepresentation, canonicalFieldRepresentation,
    RingTheorems.FieldAbstractType, RingTheorems.State.Label.toDomain,
    RingTheorems.State.Label.toCodomain, CanonicalField.set]

theorem cc_send (th : RingTheorems.Theory) (s s' : RingTheorems.State RingTheorems.FieldAbstractType) :
    CC.tr th s RingTheorems.Label.send s' ↔
    ∃ n ∈ th.allNodes,
      if (⟨n, n, RingTheorems.nextNode n th⟩ : RingTheorems.Message) ∉ s.messages then
        (⟨s.leader, s.messages.insertOrdered ⟨n, n, RingTheorems.nextNode n th⟩⟩ :
          RingTheorems.State RingTheorems.FieldAbstractType) = s'
      else s = s' := by
  simp only [CC, RingTheorems.relationalTransitionSystem, nextSimp, RingTheorems.NextAct,
    RingTheorems.instAbstractFieldRepresentation, canonicalFieldRepresentation,
    RingTheorems.FieldAbstractType, RingTheorems.State.Label.toDomain,
    RingTheorems.State.Label.toCodomain, CanonicalField.set]

theorem cc_recv (th : RingTheorems.Theory) (s s' : RingTheorems.State RingTheorems.FieldAbstractType) :
    CC.tr th s RingTheorems.Label.recv s' ↔
    ∃ m ∈ s.messages,
      if m.payload = m.dst ∧ m.dst ∉ s.leader then
        (⟨m.dst :: s.leader, s.messages.erase m⟩ :
          RingTheorems.State RingTheorems.FieldAbstractType) = s'
      else if m.dst ≤ m.payload then
        if (⟨m.payload, m.dst, RingTheorems.nextNode m.dst th⟩ : RingTheorems.Message) ∉
            s.messages.erase m then
          (⟨s.leader, (s.messages.erase m).insertOrdered
              ⟨m.payload, m.dst, RingTheorems.nextNode m.dst th⟩⟩ :
            RingTheorems.State RingTheorems.FieldAbstractType) = s'
        else (⟨s.leader, s.messages.erase m⟩ : RingTheorems.State RingTheorems.FieldAbstractType) = s'
      else (⟨s.leader, s.messages.erase m⟩ : RingTheorems.State RingTheorems.FieldAbstractType) = s' := by
  simp only [CC, RingTheorems.relationalTransitionSystem, nextSimp, RingTheorems.NextAct,
    RingTheorems.instAbstractFieldRepresentation, canonicalFieldRepresentation,
    RingTheorems.FieldAbstractType, RingTheorems.State.Label.toDomain,
    RingTheorems.State.Label.toCodomain, CanonicalField.set]

/-! ## Characterizations of the abstract transition system -/

section Abstract

open Classical in
attribute [local instance] Classical.propDecidable

variable {node : Type} [DecidableEq node] [Inhabited node] [TotalOrder node] [Between node]

/-- Abbreviation for the abstract (`RingDec`) transition system over `node`. -/
noncomputable abbrev CA : RelationalTransitionSystem (RingDec.Theory node)
    (RingDec.State (RingDec.FieldAbstractType node)) (RingDec.Label node) :=
  RingDec.relationalTransitionSystem node

omit [DecidableEq node] in
theorem ca_init (th : RingDec.Theory node) (s : RingDec.State (RingDec.FieldAbstractType node)) :
    (CA (node := node)).init th s ↔
      (⟨fun _ => false, fun _ _ => false⟩ : RingDec.State (RingDec.FieldAbstractType node)) = s := by
  simp only [CA, RingDec.relationalTransitionSystem, nextSimp, RingDec.Init,
    RingDec.instAbstractFieldRepresentation, canonicalFieldRepresentation,
    RingDec.FieldAbstractType, RingDec.State.Label.toDomain,
    RingDec.State.Label.toCodomain, CanonicalField.set]

theorem ca_send (th : RingDec.Theory node) (s s' : RingDec.State (RingDec.FieldAbstractType node))
    (a b : node) :
    (CA (node := node)).tr th s (RingDec.Label.send a b) s' ↔
      (∀ Z : node, a ≠ b ∧ (Z ≠ a ∧ Z ≠ b → Between.btw a b Z)) ∧
      (⟨s.leader, fun x y => if a = x ∧ b = y then true else s.pending x y⟩ :
        RingDec.State (RingDec.FieldAbstractType node)) = s' := by
  simp only [CA, RingDec.relationalTransitionSystem, nextSimp, RingDec.NextAct,
    RingDec.instAbstractFieldRepresentation, canonicalFieldRepresentation,
    RingDec.FieldAbstractType, RingDec.State.Label.toDomain,
    RingDec.State.Label.toCodomain, CanonicalField.set]

theorem ca_recv (th : RingDec.Theory node) (s s' : RingDec.State (RingDec.FieldAbstractType node))
    (sender a b : node) :
    (CA (node := node)).tr th s (RingDec.Label.recv sender a b) s' ↔
      (∀ Z : node, a ≠ b ∧ (Z ≠ a ∧ Z ≠ b → Between.btw a b Z)) ∧
      s.pending sender a = true ∧
      (if sender = a then
          (⟨fun x => if a = x then true else s.leader x,
            fun x y => if sender = x ∧ a = y then false else s.pending x y⟩ :
            RingDec.State (RingDec.FieldAbstractType node)) = s'
        else if TotalOrder.le a sender then
          (⟨s.leader, fun x y =>
              if sender = x ∧ b = y then true
              else if sender = x ∧ a = y then false else s.pending x y⟩ :
            RingDec.State (RingDec.FieldAbstractType node)) = s'
        else
          (⟨s.leader, fun x y => if sender = x ∧ a = y then false else s.pending x y⟩ :
            RingDec.State (RingDec.FieldAbstractType node)) = s') := by
  simp only [CA, RingDec.relationalTransitionSystem, nextSimp, RingDec.NextAct,
    RingDec.instAbstractFieldRepresentation, canonicalFieldRepresentation,
    RingDec.FieldAbstractType, RingDec.State.Label.toDomain,
    RingDec.State.Label.toCodomain, CanonicalField.set]

end Abstract

/-! ## The concrete node type and its order structures

For a fixed background theory `allNodes = L`, the abstract node type is the
subtype of `ℕ` consisting of members of `L`. -/

/-- Nodes are the members of the concrete `allNodes` list. -/
abbrev RNode (L : List ℕ) := {x : ℕ // x ∈ L}

/-- Position of a node in `L`; used as the rank for the ring (`Between`) order. -/
abbrev RNode.rank {L : List ℕ} (x : RNode L) : ℕ := L.idxOf x.val

theorem RNode.rank_lt {L : List ℕ} (x : RNode L) : x.rank < L.length :=
  List.idxOf_lt_length_of_mem x.property

/-- `rank` is injective: distinct members of `L` sit at distinct positions. -/
theorem RNode.rank_injective {L : List ℕ} {x y : RNode L} (h : x.rank = y.rank) : x = y := by
  apply Subtype.ext
  have hx : L[L.idxOf x.val]'x.rank_lt = x.val := List.getElem_idxOf x.rank_lt
  have hy : L[L.idxOf y.val]'y.rank_lt = y.val := List.getElem_idxOf y.rank_lt
  rw [← hx, ← hy]
  simp only [RNode.rank] at h
  congr 1

/-- The abstract `TotalOrder` on nodes orders them by their `Nat` value — matching
the concrete comparison `n ≤ m.payload`. -/
instance RNode.instTotalOrder (L : List ℕ) : TotalOrder (RNode L) :=
  total_order_by_inj_on_nat (fun x => x.val) (fun _ _ h => Subtype.ext h)

theorem RNode.le_iff {L : List ℕ} (x y : RNode L) :
    TotalOrder.le x y ↔ x.val ≤ y.val := Iff.rfl

/-- The abstract `Between` (ring topology) orders nodes by their position in `L` —
matching the concrete successor function `nextNode = L.next`. -/
instance RNode.instBetween (L : List ℕ) : Between (RNode L) :=
  ordered_ring (RNode L) RNode.rank (fun _ _ hne h => hne (RNode.rank_injective h))

theorem RNode.btw_iff {L : List ℕ} (a b c : RNode L) :
    Between.btw a b c ↔
      (a.rank < b.rank ∧ b.rank < c.rank) ∨
      (c.rank < a.rank ∧ a.rank < b.rank) ∨
      (b.rank < c.rank ∧ c.rank < a.rank) := Iff.rfl

/-- An inhabitant of `RNode L` whenever `L` is nonempty. -/
def RNode.inhabited {L : List ℕ} (h : 0 < L.length) : Inhabited (RNode L) :=
  ⟨⟨L[0], List.getElem_mem _⟩⟩

/-! ### Connecting `nextNode` to the ring order -/

/-- For a member `n` of the theory's node list, `nextNode` is the cyclic
list-successor `List.next`. -/
theorem nextNode_eq_next {th : RingTheorems.Theory} {n : ℕ} (hn : n ∈ th.allNodes) :
    RingTheorems.nextNode n th = th.allNodes.next n hn := by
  simp only [RingTheorems.nextNode, instIsSubReaderOfRefl.readFrom_id]
  exact dif_pos hn

/-- The rank of the cyclic successor is the cyclic successor of the rank. -/
theorem RNode.rank_next {L : List ℕ} (hnodup : L.Nodup) (n : ℕ) (hn : n ∈ L)
    (hmem : L.next n hn ∈ L) :
    RNode.rank (⟨L.next n hn, hmem⟩ : RNode L) = (L.idxOf n + 1) % L.length := by
  simp only [RNode.rank]
  rw [List.next_eq_getElem hn]
  exact List.Nodup.idxOf_getElem hnodup _ _

/-- Pure arithmetic core of the `isNext` fact: with all ranks in `[0, len)`, the
successor rank `(ra + 1) % len`, and `rZ` distinct from both, `Z` lies between. -/
theorem btw_of_succ {len ra rb rZ : ℕ} (hlen : 1 < len) (hra : ra < len) (hrZ : rZ < len)
    (hrb : rb = (ra + 1) % len) (hZa : rZ ≠ ra) (hZb : rZ ≠ rb) :
    (ra < rb ∧ rb < rZ) ∨ (rZ < ra ∧ ra < rb) ∨ (rb < rZ ∧ rZ < ra) := by
  rcases Nat.lt_or_ge (ra + 1) len with h | h
  · have : rb = ra + 1 := by rw [hrb, Nat.mod_eq_of_lt h]
    omega
  · have hra1 : ra + 1 = len := by omega
    have : rb = 0 := by rw [hrb, hra1, Nat.mod_self]
    omega

/-- The successor rank differs from the rank, hence the node differs from its
successor. -/
theorem rank_ne_succ {len ra : ℕ} (hlen : 1 < len) (hra : ra < len) :
    (ra + 1) % len ≠ ra := by
  rcases Nat.lt_or_ge (ra + 1) len with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · have : ra + 1 = len := by omega
    rw [this, Nat.mod_self]; omega

/-- The cyclic successor map `a ↦ (a + 1) % len` is injective on `[0, len)`. -/
theorem succ_mod_inj {len a b : ℕ} (ha : a < len) (hb : b < len)
    (h : (a + 1) % len = (b + 1) % len) : a = b := by
  rcases Nat.lt_or_ge (a + 1) len with hA | hA <;> rcases Nat.lt_or_ge (b + 1) len with hB | hB
  · rw [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB] at h; omega
  · have : b + 1 = len := by omega
    rw [Nat.mod_eq_of_lt hA, this, Nat.mod_self] at h; omega
  · have : a + 1 = len := by omega
    rw [this, Nat.mod_self, Nat.mod_eq_of_lt hB] at h; omega
  · have : a + 1 = len := by omega
    have : b + 1 = len := by omega
    omega

/-- The `isNext` fact: in the ring induced by positions in `L`, every node `Z`
distinct from `n` and its successor `L.next n` lies *between* them. -/
theorem isNext_next {L : List ℕ} (hnodup : L.Nodup) (hlen : 1 < L.length)
    (n : ℕ) (hn : n ∈ L) (hnn : L.next n hn ∈ L) (Z : RNode L) :
    (⟨n, hn⟩ : RNode L) ≠ ⟨L.next n hn, hnn⟩ ∧
      (Z ≠ ⟨n, hn⟩ ∧ Z ≠ ⟨L.next n hn, hnn⟩ →
        Between.btw (⟨n, hn⟩ : RNode L) ⟨L.next n hn, hnn⟩ Z) := by
  have hra : RNode.rank (⟨n, hn⟩ : RNode L) = L.idxOf n := rfl
  have hrb : RNode.rank (⟨L.next n hn, hnn⟩ : RNode L) = (L.idxOf n + 1) % L.length :=
    RNode.rank_next hnodup n hn hnn
  have hra_lt : L.idxOf n < L.length := List.idxOf_lt_length_of_mem hn
  have hne : (⟨n, hn⟩ : RNode L) ≠ ⟨L.next n hn, hnn⟩ := by
    intro heq
    have : RNode.rank (⟨n, hn⟩ : RNode L) = RNode.rank ⟨L.next n hn, hnn⟩ := by rw [heq]
    rw [hra, hrb] at this
    exact rank_ne_succ hlen hra_lt this.symm
  refine ⟨hne, ?_⟩
  rintro ⟨hZa, hZb⟩
  rw [RNode.btw_iff, hra, hrb]
  apply btw_of_succ hlen hra_lt (RNode.rank_lt Z) rfl
  · intro hc; exact hZa (RNode.rank_injective (by rw [hra, hc]))
  · intro hc; exact hZb (RNode.rank_injective (by rw [hrb, hc]))

/-- `isNext` holds between a node and its `nextNode` successor. -/
theorem isNext_nextNode {th : RingTheorems.Theory} (hnodup : th.allNodes.Nodup)
    (hlen : 1 < th.allNodes.length) (n : ℕ) (hn : n ∈ th.allNodes)
    (hnn : RingTheorems.nextNode n th ∈ th.allNodes) (Z : RNode th.allNodes) :
    (⟨n, hn⟩ : RNode th.allNodes) ≠ ⟨RingTheorems.nextNode n th, hnn⟩ ∧
      (Z ≠ ⟨n, hn⟩ ∧ Z ≠ ⟨RingTheorems.nextNode n th, hnn⟩ →
        Between.btw (⟨n, hn⟩ : RNode th.allNodes) ⟨RingTheorems.nextNode n th, hnn⟩ Z) := by
  have heq : (⟨RingTheorems.nextNode n th, hnn⟩ : RNode th.allNodes)
      = ⟨th.allNodes.next n hn, List.next_mem _ _ _⟩ := Subtype.ext (nextNode_eq_next hn)
  rw [heq]
  exact isNext_next hnodup hlen n hn _ Z

/-- `nextNode` is injective on the node list (the ring successor is a bijection). -/
theorem nextNode_inj {th : RingTheorems.Theory} (hnodup : th.allNodes.Nodup)
    {x y : ℕ} (hx : x ∈ th.allNodes) (hy : y ∈ th.allNodes)
    (h : RingTheorems.nextNode x th = RingTheorems.nextNode y th) : x = y := by
  rw [nextNode_eq_next hx, nextNode_eq_next hy] at h
  have hxx : th.allNodes.next x hx ∈ th.allNodes := List.next_mem _ _ _
  have hyy : th.allNodes.next y hy ∈ th.allNodes := List.next_mem _ _ _
  have hrank : (th.allNodes.idxOf x + 1) % th.allNodes.length =
      (th.allNodes.idxOf y + 1) % th.allNodes.length := by
    have e1 := RNode.rank_next hnodup x hx hxx
    have e2 := RNode.rank_next hnodup y hy hyy
    rw [← e1, ← e2]
    congr 1
    exact Subtype.ext h
  have hidx : th.allNodes.idxOf x = th.allNodes.idxOf y :=
    succ_mod_inj (List.idxOf_lt_length_of_mem hx) (List.idxOf_lt_length_of_mem hy) hrank
  have hgx : th.allNodes[th.allNodes.idxOf x]'(List.idxOf_lt_length_of_mem hx) = x :=
    List.getElem_idxOf _
  have hgy : th.allNodes[th.allNodes.idxOf y]'(List.idxOf_lt_length_of_mem hy) = y :=
    List.getElem_idxOf _
  rw [← hgx, ← hgy]; congr 1

/-- `RNode L` is inhabited whenever `L` is nonempty. -/
instance RNode.instInhabited (L : List ℕ) [NeZero L.length] : Inhabited (RNode L) :=
  ⟨⟨L[0]'(Nat.pos_of_ne_zero (NeZero.ne L.length)), List.getElem_mem _⟩⟩

/-! ## The refinement relation -/

/-- The refinement relation gluing a concrete state to an abstract one (over a
fixed theory `th`).  It records:

* leader correspondence: the abstract `leader` predicate is the membership
  predicate of the concrete `leader` list;
* pending correspondence: the abstract `pending` relation holds exactly when a
  matching concrete message exists;
* concrete well-formedness invariants strong enough to be inductive and to
  recover `single_leader`.
-/
def rel (th : RingTheorems.Theory)
    (sc : RingTheorems.State RingTheorems.FieldAbstractType)
    (sa : RingDec.State (RingDec.FieldAbstractType (RNode th.allNodes))) : Prop :=
  (∀ x : RNode th.allNodes, sa.leader x = true ↔ x.val ∈ sc.leader) ∧
  (∀ s d : RNode th.allNodes, sa.pending s d = true ↔
      ∃ m ∈ sc.messages, m.payload = s.val ∧ m.dst = d.val) ∧
  sc.leader.Nodup ∧
  (∀ y ∈ sc.leader, y ∈ th.allNodes) ∧
  sc.messages.Nodup ∧
  (∀ m ∈ sc.messages, m.src ∈ th.allNodes ∧ m.payload ∈ th.allNodes ∧
      m.dst = RingTheorems.nextNode m.src th)

/-- Under well-formedness, a message is determined by its `(payload, dst)` pair. -/
theorem msg_unique {th : RingTheorems.Theory} (hnodup : th.allNodes.Nodup)
    {ms : List RingTheorems.Message}
    (hwf : ∀ m ∈ ms, m.src ∈ th.allNodes ∧ m.payload ∈ th.allNodes ∧
      m.dst = RingTheorems.nextNode m.src th)
    {m1 m2 : RingTheorems.Message} (h1 : m1 ∈ ms) (h2 : m2 ∈ ms)
    (hp : m1.payload = m2.payload) (hd : m1.dst = m2.dst) : m1 = m2 := by
  obtain ⟨hs1, _, hdst1⟩ := hwf m1 h1
  obtain ⟨hs2, _, hdst2⟩ := hwf m2 h2
  have hsrc : m1.src = m2.src := by
    apply nextNode_inj hnodup hs1 hs2
    rw [← hdst1, ← hdst2, hd]
  cases m1; cases m2; simp_all

/-! ### List utilities for `insertOrdered` -/

theorem mem_insertOrdered {α : Type} [Ord α] (x y : α) (l : List α) :
    y ∈ l.insertOrdered x ↔ y = x ∨ y ∈ l := by
  rw [List.insertOrdered]
  exact (List.perm_orderedInsert _ x l).mem_iff.trans List.mem_cons

theorem nodup_insertOrdered {α : Type} [Ord α] (x : α) (l : List α) :
    (l.insertOrdered x).Nodup ↔ (x :: l).Nodup := by
  rw [List.insertOrdered]
  exact (List.perm_orderedInsert _ x l).nodup_iff

/-! ## The pointed forward simulation -/

theorem ca_assumptions_true {node : Type} [DecidableEq node] [Inhabited node]
    [TotalOrder node] [Between node] (th : RingDec.Theory node) :
    (CA (node := node)).assumptions th := by
  simp only [CA, RingDec.relationalTransitionSystem, invSimp, RingDec.Assumptions]

theorem sim (th : RingTheorems.Theory) (hnodup : th.allNodes.Nodup)
    (hlen : 1 < th.allNodes.length) [NeZero th.allNodes.length] :
    PointedForwardSimulation CC (CA (node := RNode th.allNodes)) th
      (⟨⟩ : RingDec.Theory (RNode th.allNodes)) (rel th) := by
  refine ⟨?assumptions, ?init, ?step⟩
  case assumptions =>
    intro _; exact ca_assumptions_true _
  case init =>
    intro sc _ hinit
    rw [cc_init] at hinit
    subst hinit
    refine ⟨⟨fun _ => false, fun _ _ => false⟩, ?_, ?_⟩
    · rw [ca_init]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  case step =>
    intro sc sc' sa label hass hrel htr
    obtain ⟨hLead, hPend, hLNodup, hLsub, hMNodup, hMwf⟩ := hrel
    cases label with
    | send =>
      rw [cc_send] at htr
      obtain ⟨n, hn, htr⟩ := htr
      have hnn : RingTheorems.nextNode n th ∈ th.allNodes := by
        rw [nextNode_eq_next hn]; exact List.next_mem _ _ _
      set nodeN : RNode th.allNodes := ⟨n, hn⟩ with hnodeN
      set nodeNN : RNode th.allNodes := ⟨RingTheorems.nextNode n th, hnn⟩ with hnodeNN
      set msg : RingTheorems.Message := ⟨n, n, RingTheorems.nextNode n th⟩ with hmsg
      split at htr
      · -- `msg ∉ messages`: take a single abstract `send` step.
        rename_i h_notin
        subst htr
        refine ⟨⟨sa.leader,
            fun x y => if nodeN = x ∧ nodeNN = y then true else sa.pending x y⟩, ?_, ?_⟩
        · apply RelationalTransitionSystem.canReach.single_tr
            (label := RingDec.Label.send nodeN nodeNN)
          rw [ca_send]
          exact ⟨fun Z => isNext_nextNode hnodup hlen n hn hnn Z, rfl⟩
        · refine ⟨hLead, ?_, hLNodup, hLsub, ?_, ?_⟩
          · -- pending correspondence
            intro s d
            dsimp only
            by_cases hc : nodeN = s ∧ nodeNN = d
            · obtain ⟨rfl, rfl⟩ := hc
              rw [if_pos ⟨rfl, rfl⟩]
              exact iff_of_true rfl ⟨msg, (mem_insertOrdered _ _ _).mpr (Or.inl rfl), rfl, rfl⟩
            · rw [if_neg hc, hPend s d]
              constructor
              · rintro ⟨m', hm', hP⟩
                exact ⟨m', (mem_insertOrdered _ _ _).mpr (Or.inr hm'), hP⟩
              · rintro ⟨m', hm', hP⟩
                rcases (mem_insertOrdered _ _ _).mp hm' with rfl | hin
                · exact absurd ⟨Subtype.ext hP.1, Subtype.ext hP.2⟩ hc
                · exact ⟨m', hin, hP⟩
          · -- messages nodup
            rw [nodup_insertOrdered]
            exact List.nodup_cons.mpr ⟨h_notin, hMNodup⟩
          · -- messages well-formed
            intro m' hm'
            rcases (mem_insertOrdered _ _ _).mp hm' with rfl | hin
            · exact ⟨hn, hn, by rw [hmsg]⟩
            · exact hMwf m' hin
      · -- `msg ∈ messages`: concrete state unchanged, no abstract step.
        rename_i _h_in
        refine ⟨sa, RelationalTransitionSystem.canReach.refl _ _ _, ?_⟩
        rw [← htr]
        exact ⟨hLead, hPend, hLNodup, hLsub, hMNodup, hMwf⟩
    | recv =>
      rw [cc_recv] at htr
      obtain ⟨m, hm, htr⟩ := htr
      obtain ⟨hsrc_mem, hpay_mem, hdst_eq⟩ := hMwf m hm
      have hdst_mem : m.dst ∈ th.allNodes := by
        rw [hdst_eq, nextNode_eq_next hsrc_mem]; exact List.next_mem _ _ _
      have hnnd : RingTheorems.nextNode m.dst th ∈ th.allNodes := by
        rw [nextNode_eq_next hdst_mem]; exact List.next_mem _ _ _
      set a : RNode th.allNodes := ⟨m.dst, hdst_mem⟩ with ha
      set sender : RNode th.allNodes := ⟨m.payload, hpay_mem⟩ with hsender
      set b : RNode th.allNodes := ⟨RingTheorems.nextNode m.dst th, hnnd⟩ with hb
      set msg2 : RingTheorems.Message := ⟨m.payload, m.dst, RingTheorems.nextNode m.dst th⟩ with hmsg2
      have hpend_m : sa.pending sender a = true := (hPend sender a).mpr ⟨m, hm, rfl, rfl⟩
      have hisNext : ∀ Z, (a ≠ b) ∧ (Z ≠ a ∧ Z ≠ b → Between.btw a b Z) :=
        fun Z => isNext_nextNode hnodup hlen m.dst hdst_mem hnnd Z
      -- no message of `erase m` matches `m`'s `(payload, dst)` pair
      have key_erase : ∀ m'' ∈ sc.messages.erase m,
          ¬(m''.payload = m.payload ∧ m''.dst = m.dst) := by
        rintro m'' hm'' ⟨hp, hd⟩
        have hmem'' : m'' ∈ sc.messages := ((List.Nodup.mem_erase_iff hMNodup).mp hm'').2
        exact ((List.Nodup.mem_erase_iff hMNodup).mp hm'').1
          (msg_unique hnodup hMwf hmem'' hm hp hd)
      split at htr
      · -- CASE A: receiver gets its own token and is not yet a leader → elect it.
        rename_i hcondA
        obtain ⟨hpd, hdnl⟩ := hcondA
        have hsa : sender = a := Subtype.ext hpd
        subst htr
        refine ⟨⟨fun x => if a = x then true else sa.leader x,
            fun x y => if sender = x ∧ a = y then false else sa.pending x y⟩, ?_, ?_⟩
        · apply RelationalTransitionSystem.canReach.single_tr
            (label := RingDec.Label.recv sender a b)
          rw [ca_recv]
          refine ⟨fun Z => hisNext Z, hpend_m, ?_⟩
          rw [if_pos hsa]
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- leader correspondence
            intro x
            dsimp only
            by_cases hx : a = x
            · rw [if_pos hx]; subst hx
              exact iff_of_true rfl (List.mem_cons_self ..)
            · rw [if_neg hx, hLead x]
              constructor
              · exact fun h => List.mem_cons_of_mem _ h
              · intro h
                rcases List.mem_cons.mp h with he | h
                · exact absurd (Subtype.ext he.symm : a = x) hx
                · exact h
          · -- pending correspondence
            intro s d
            dsimp only
            by_cases hc : sender = s ∧ a = d
            · obtain ⟨rfl, rfl⟩ := hc
              rw [if_pos ⟨rfl, rfl⟩]
              exact iff_of_false (by simp)
                (fun ⟨m', hm', hp, hd⟩ => key_erase m' hm' ⟨hp, hd⟩)
            · rw [if_neg hc, hPend s d]
              constructor
              · rintro ⟨m', hm', hP⟩
                refine ⟨m', (List.Nodup.mem_erase_iff hMNodup).mpr ⟨?_, hm'⟩, hP⟩
                rintro rfl
                exact hc ⟨Subtype.ext hP.1, Subtype.ext hP.2⟩
              · rintro ⟨m', hm', hP⟩
                exact ⟨m', ((List.Nodup.mem_erase_iff hMNodup).mp hm').2, hP⟩
          · exact List.nodup_cons.mpr ⟨hdnl, hLNodup⟩
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | h
            · exact hdst_mem
            · exact hLsub y h
          · exact List.Nodup.erase m hMNodup
          · intro m' hm'
            exact hMwf m' ((List.Nodup.mem_erase_iff hMNodup).mp hm').2
      · rename_i hcondA_neg
        split at htr
        · -- receiver does not elect itself but forwards (`m.dst ≤ m.payload`).
          rename_i hle
          -- Characterize `sc'` uniformly across whether `msg2` was already present.
          have hsc'L : sc'.leader = sc.leader := by split at htr <;> rw [← htr]
          have hsc'M : ∀ m'', m'' ∈ sc'.messages ↔
              (m'' = msg2 ∨ m'' ∈ sc.messages.erase m) := by
            split at htr
            · rename_i hni; rw [← htr]; intro m''; exact mem_insertOrdered _ _ _
            · rename_i hi; rw [← htr]; intro m''
              refine ⟨Or.inr, ?_⟩
              rintro (rfl | h)
              · exact not_not.mp hi
              · exact h
          have hsc'Nodup : sc'.messages.Nodup := by
            split at htr
            · rename_i hni; rw [← htr, nodup_insertOrdered]
              exact List.nodup_cons.mpr ⟨hni, List.Nodup.erase m hMNodup⟩
            · rename_i hi; rw [← htr]; exact List.Nodup.erase m hMNodup
          have hex : ∀ (s d : RNode th.allNodes),
              (∃ m'' ∈ sc'.messages, m''.payload = s.val ∧ m''.dst = d.val) ↔
              ((msg2.payload = s.val ∧ msg2.dst = d.val) ∨
               ∃ m'' ∈ sc.messages.erase m, m''.payload = s.val ∧ m''.dst = d.val) := by
            intro s d
            constructor
            · rintro ⟨m'', hm'', hP⟩
              rcases (hsc'M m'').mp hm'' with rfl | h
              · exact Or.inl hP
              · exact Or.inr ⟨m'', h, hP⟩
            · rintro (hP | ⟨m'', h, hP⟩)
              · exact ⟨msg2, (hsc'M msg2).mpr (Or.inl rfl), hP⟩
              · exact ⟨m'', (hsc'M m'').mpr (Or.inr h), hP⟩
          have hwf_common : ∀ m'' ∈ sc'.messages,
              m''.src ∈ th.allNodes ∧ m''.payload ∈ th.allNodes ∧
              m''.dst = RingTheorems.nextNode m''.src th := by
            intro m'' hm''
            rcases (hsc'M m'').mp hm'' with rfl | h
            · exact ⟨hdst_mem, hpay_mem, rfl⟩
            · exact hMwf m'' ((List.Nodup.mem_erase_iff hMNodup).mp h).2
          by_cases hpd : m.payload = m.dst
          · -- corner: receiver already a leader re-forwards its own token.
            have hsa : sender = a := Subtype.ext hpd
            have hdl : m.dst ∈ sc.leader := by
              by_contra h; exact hcondA_neg ⟨hpd, h⟩
            refine ⟨⟨fun x => if a = x then true else sa.leader x,
                fun x y => if a = x ∧ b = y then true
                  else if a = x ∧ a = y then false else sa.pending x y⟩, ?_, ?_⟩
            · -- two abstract steps: clear the self-token, then re-emit it.
              refine RelationalTransitionSystem.canReach.comp
                (s₂ := ⟨fun x => if a = x then true else sa.leader x,
                  fun x y => if a = x ∧ a = y then false else sa.pending x y⟩) ?_ ?_
              · apply RelationalTransitionSystem.canReach.single_tr
                  (label := RingDec.Label.recv a a b)
                rw [ca_recv]
                exact ⟨fun Z => hisNext Z, hsa ▸ hpend_m, by rw [if_pos rfl]⟩
              · apply RelationalTransitionSystem.canReach.single_tr
                  (label := RingDec.Label.send a b)
                rw [ca_send]
                exact ⟨fun Z => hisNext Z, rfl⟩
            · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · intro x; rw [hsc'L]; dsimp only
                by_cases hx : a = x
                · rw [if_pos hx]; refine iff_of_true rfl ?_; rw [← hx]; exact hdl
                · rw [if_neg hx]; exact hLead x
              · intro s d; dsimp only
                by_cases hc1 : a = s ∧ b = d
                · obtain ⟨rfl, rfl⟩ := hc1
                  rw [if_pos ⟨rfl, rfl⟩, hex a b]
                  exact iff_of_true rfl (Or.inl ⟨hpd, rfl⟩)
                · by_cases hc2 : a = s ∧ a = d
                  · obtain ⟨rfl, rfl⟩ := hc2
                    rw [if_neg hc1, if_pos ⟨rfl, rfl⟩, hex a a]
                    apply iff_of_false (by simp)
                    rintro (hPm | ⟨m'', h, hP⟩)
                    · exact (hisNext a).1 (Subtype.ext hPm.2).symm
                    · exact key_erase m'' h ⟨hP.1.trans hpd.symm, hP.2⟩
                  · rw [if_neg hc1, if_neg hc2, hex s d, hPend s d]
                    constructor
                    · rintro ⟨m', hm', hP⟩
                      refine Or.inr ⟨m', (List.Nodup.mem_erase_iff hMNodup).mpr ⟨?_, hm'⟩, hP⟩
                      rintro rfl
                      exact hc2 ⟨hsa ▸ Subtype.ext hP.1, Subtype.ext hP.2⟩
                    · rintro (hPm | ⟨m', h, hP⟩)
                      · exact absurd ⟨hsa ▸ Subtype.ext hPm.1, Subtype.ext hPm.2⟩ hc1
                      · exact ⟨m', ((List.Nodup.mem_erase_iff hMNodup).mp h).2, hP⟩
              · rw [hsc'L]; exact hLNodup
              · rw [hsc'L]; exact hLsub
              · exact hsc'Nodup
              · exact hwf_common
          · -- genuine forward: receiver is smaller, passes the token on.
            have hsna : sender ≠ a := fun h => hpd (congrArg Subtype.val h)
            refine ⟨⟨sa.leader, fun x y =>
                if sender = x ∧ b = y then true
                else if sender = x ∧ a = y then false else sa.pending x y⟩, ?_, ?_⟩
            · apply RelationalTransitionSystem.canReach.single_tr
                (label := RingDec.Label.recv sender a b)
              rw [ca_recv]
              refine ⟨fun Z => hisNext Z, hpend_m, ?_⟩
              rw [if_neg hsna, if_pos (show TotalOrder.le a sender from hle)]
            · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hsc'L]; exact hLead
              · intro s d; dsimp only
                by_cases hc1 : sender = s ∧ b = d
                · obtain ⟨rfl, rfl⟩ := hc1
                  rw [if_pos ⟨rfl, rfl⟩, hex sender b]
                  exact iff_of_true rfl (Or.inl ⟨rfl, rfl⟩)
                · by_cases hc2 : sender = s ∧ a = d
                  · obtain ⟨rfl, rfl⟩ := hc2
                    rw [if_neg hc1, if_pos ⟨rfl, rfl⟩, hex sender a]
                    apply iff_of_false (by simp)
                    rintro (hPm | ⟨m'', h, hP⟩)
                    · exact (hisNext a).1 (Subtype.ext hPm.2).symm
                    · exact key_erase m'' h ⟨hP.1, hP.2⟩
                  · rw [if_neg hc1, if_neg hc2, hex s d, hPend s d]
                    constructor
                    · rintro ⟨m', hm', hP⟩
                      refine Or.inr ⟨m', (List.Nodup.mem_erase_iff hMNodup).mpr ⟨?_, hm'⟩, hP⟩
                      rintro rfl
                      exact hc2 ⟨Subtype.ext hP.1, Subtype.ext hP.2⟩
                    · rintro (hPm | ⟨m', h, hP⟩)
                      · exact absurd ⟨Subtype.ext hPm.1, Subtype.ext hPm.2⟩ hc1
                      · exact ⟨m', ((List.Nodup.mem_erase_iff hMNodup).mp h).2, hP⟩
              · rw [hsc'L]; exact hLNodup
              · rw [hsc'L]; exact hLsub
              · exact hsc'Nodup
              · exact hwf_common
        · -- CASE C: receiver is larger than the token's owner → drop it.
          rename_i hnle
          have hsna : sender ≠ a := by
            intro h
            have : m.payload = m.dst := congrArg Subtype.val h
            exact hnle (by rw [this])
          subst htr
          refine ⟨⟨sa.leader,
              fun x y => if sender = x ∧ a = y then false else sa.pending x y⟩, ?_, ?_⟩
          · apply RelationalTransitionSystem.canReach.single_tr
              (label := RingDec.Label.recv sender a b)
            rw [ca_recv]
            refine ⟨fun Z => hisNext Z, hpend_m, ?_⟩
            rw [if_neg hsna, if_neg (show ¬ TotalOrder.le a sender from hnle)]
          · refine ⟨hLead, ?_, hLNodup, hLsub, List.Nodup.erase m hMNodup, ?_⟩
            · intro s d; dsimp only
              by_cases hc : sender = s ∧ a = d
              · obtain ⟨rfl, rfl⟩ := hc
                rw [if_pos ⟨rfl, rfl⟩]
                exact iff_of_false (by simp)
                  (fun ⟨m', hm', hp, hd⟩ => key_erase m' hm' ⟨hp, hd⟩)
              · rw [if_neg hc, hPend s d]
                constructor
                · rintro ⟨m', hm', hP⟩
                  refine ⟨m', (List.Nodup.mem_erase_iff hMNodup).mpr ⟨?_, hm'⟩, hP⟩
                  rintro rfl
                  exact hc ⟨Subtype.ext hP.1, Subtype.ext hP.2⟩
                · rintro ⟨m', hm', hP⟩
                  exact ⟨m', ((List.Nodup.mem_erase_iff hMNodup).mp hm').2, hP⟩
            · intro m' hm'
              exact hMwf m' ((List.Nodup.mem_erase_iff hMNodup).mp hm').2

/-! ## Transporting the abstract safety property to the concrete system -/

/-- A `Nodup` list all of whose elements are equal has length at most one. -/
theorem length_le_one {α : Type} {l : List α} (hnd : l.Nodup)
    (hp : ∀ a ∈ l, ∀ b ∈ l, a = b) : l.length ≤ 1 := by
  match l, hnd, hp with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: t, hnd, hp =>
      have hab : a = b := hp a (by simp) b (by simp)
      subst hab
      simp at hnd

/-- **Main theorem.**  Every reachable state of the concrete `RingConc`
specification has at most one leader — its safety property `single_leader`,
established here purely by refinement to `RingAbs`. -/
theorem single_leader_holds :
    CC.isInvariant (fun _th st => st.leader.length ≤ 1) := by
  intro th st hreach
  -- The background theory of any reachable state satisfies the assumptions.
  have hass := RelationalTransitionSystem.reachable_assumptions _ _ _ hreach
  rw [cc_assumptions] at hass
  obtain ⟨hnodup, hlen⟩ := hass
  haveI : NeZero th.allNodes.length := ⟨by omega⟩
  -- The pointed forward simulation into the abstract system.
  have S := sim th hnodup hlen
  -- The abstract `single_leader` invariant, specialized to our node type.
  have habs : ∀ sa, (CA (node := RNode th.allNodes)).reachable
      (⟨⟩ : RingDec.Theory (RNode th.allNodes)) sa →
      (∀ N M : RNode th.allNodes, sa.leader N = true ∧ sa.leader M = true → N = M) := by
    intro sa hr
    exact RingDec.single_leader.is_inv (node := RNode th.allNodes) (⟨⟩) sa hr
  -- The refinement relation lets the abstract invariant bound the concrete leader list.
  have hrel : ∀ sc sa, rel th sc sa →
      (∀ N M : RNode th.allNodes, sa.leader N = true ∧ sa.leader M = true → N = M) →
      sc.leader.length ≤ 1 := by
    rintro sc sa ⟨hLead, _, hLNodup, hLsub, _, _⟩ hsingle
    apply length_le_one hLNodup
    intro x hx y hy
    have hX : sa.leader ⟨x, hLsub x hx⟩ = true := (hLead _).mpr hx
    have hY : sa.leader ⟨y, hLsub y hy⟩ = true := (hLead _).mpr hy
    exact congrArg Subtype.val (hsingle _ _ ⟨hX, hY⟩)
  exact PointedForwardSimulation.invariant S habs hrel st hreach

/-- The same result, phrased against the safety predicate `RingTheorems.single_leader`
*generated* by `RingConc.lean`'s `safety [single_leader] leader.length ≤ 1` declaration.
The generated predicate is definitionally `st.leader.length ≤ 1`, so this follows
directly from `single_leader_holds`. -/
theorem single_leader_safety :
    CC.isInvariant (fun th st =>
      RingTheorems.single_leader
        (ρ := RingTheorems.Theory) (σ := RingTheorems.State RingTheorems.FieldAbstractType)
        (χ := RingTheorems.FieldAbstractType)
        (χ_rep := RingTheorems.instAbstractFieldRepresentation)
        (χ_rep_lawful := RingTheorems.instLawfulAbstractFieldRepresentation) th st) :=
  single_leader_holds

#print axioms single_leader_safety

end RingRef
