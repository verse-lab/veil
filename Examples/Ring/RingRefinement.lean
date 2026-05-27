import Examples.Ring.RingTheorems
import Examples.Ring.RingDec

open Classical
open Veil

namespace RingRefinement

private theorem List.mem_insertOrdered {α : Type u} [Ord α] {a b : α} {l : List α} :
    a ∈ List.insertOrdered b l ↔ a = b ∨ a ∈ l := by
  unfold List.insertOrdered
  exact
    (List.mem_orderedInsert
      (r := fun x y : α => compare x y == Ordering.lt)
      (a := a) (b := b) (l := l))

private theorem List.nodup_insertOrdered_of_not_mem {α : Type u} [Ord α] {a : α} {l : List α}
    (hmem : a ∉ l) (hnodup : l.Nodup) :
    (List.insertOrdered a l).Nodup := by
  unfold List.insertOrdered
  exact
    (List.perm_orderedInsert
      (r := fun x y : α => compare x y == Ordering.lt)
      a l).nodup_iff.mpr (List.Nodup.cons hmem hnodup)

private theorem Nat.succ_mod_eq_zero_of_not_lt {i n : Nat} (hi : i < n)
    (hnot : ¬ i + 1 < n) :
    (i + 1) % n = 0 := by
  have hi_last : i + 1 = n := by omega
  rw [hi_last, Nat.mod_self]

private theorem idxBtw_succ_of_ne {len i z : Nat} (hi : i < len) (hz : z < len)
    (_hlen : 1 < len) (hzi : z ≠ i) (hznext : z ≠ (i + 1) % len) :
    (i < (i + 1) % len ∧ (i + 1) % len < z) ∨
    (z < i ∧ i < (i + 1) % len) ∨
    ((i + 1) % len < z ∧ z < i) := by
  by_cases hsucc : i + 1 < len
  · have hmod : (i + 1) % len = i + 1 := Nat.mod_eq_of_lt hsucc
    by_cases hlt : z < i
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)
  · have hmod := Nat.succ_mod_eq_zero_of_not_lt hi hsucc
    exact Or.inr (Or.inr (by omega))

abbrev ConcreteState :=
  RingTheorems.State RingTheorems.FieldAbstractType

abbrev Node (th : RingTheorems.Theory) :=
  { n : Nat // n ∈ th.allNodes }

noncomputable instance nodeDecidableEq (th : RingTheorems.Theory) : DecidableEq (Node th) :=
  Classical.decEq _

abbrev AbstractState (th : RingTheorems.Theory) :=
  RingDec.State (RingDec.FieldAbstractType (Node th))

noncomputable instance nodeInhabited (th : RingTheorems.Theory)
    (hass : RingTheorems.Assumptions RingTheorems.Theory th) : Inhabited (Node th) where
  default := by
    have hlen : 0 < th.allNodes.length := by
      rcases hass with ⟨_, hnontriv⟩
      exact Nat.lt_trans Nat.zero_lt_one (by simpa using hnontriv)
    refine ⟨th.allNodes[0]'hlen, ?_⟩
    exact List.getElem_mem hlen

instance nodeTotalOrder (th : RingTheorems.Theory) : TotalOrder (Node th) where
  le x y := x.val ≤ y.val
  le_refl := by intro x; exact Nat.le_refl x.val
  le_trans := by intro x y z hxy hyz; exact Nat.le_trans hxy hyz
  le_antisymm := by
    intro x y hxy hyx
    exact Subtype.ext (Nat.le_antisymm hxy hyx)
  le_total := by intro x y; exact Nat.le_total x.val y.val

instance nodeTotalOrderDecidable (th : RingTheorems.Theory) :
    ∀ x y : Node th, Decidable (TotalOrder.le x y) := by
  intro x y
  dsimp [TotalOrder.le, nodeTotalOrder]
  infer_instance

noncomputable instance nodeBetween (th : RingTheorems.Theory) : Between (Node th) :=
  ordered_ring (Node th) (fun n => th.allNodes.idxOf n.val) (by
    intro n₁ n₂ hne hidx
    exact hne (Subtype.ext ((List.idxOf_inj n₁.property).mp hidx)))

instance nodeBetweenDecidable (th : RingTheorems.Theory) :
    ∀ x y z : Node th, Decidable (Between.btw x y z) := by
  intro x y z
  dsimp [Between.btw, nodeBetween, ordered_ring]
  infer_instance

noncomputable def abstractSystem (th : RingTheorems.Theory)
    (hass : RingTheorems.Assumptions RingTheorems.Theory th) :
    RelationalTransitionSystem (RingDec.Theory (Node th)) (AbstractState th) (RingDec.Label (Node th)) := by
  letI := nodeInhabited th hass
  exact RingDec.relationalTransitionSystem (node := Node th)

def concreteLeader (s : ConcreteState) : List Nat :=
  s.leader

def concreteMessages (s : ConcreteState) : List RingTheorems.Message :=
  s.messages

def MessageInvariants (th : RingTheorems.Theory) (s : ConcreteState) : Prop :=
  (concreteMessages s).Nodup ∧
  (∀ m ∈ concreteMessages s, m.payload ∈ th.allNodes) ∧
  (∀ m ∈ concreteMessages s, m.src ∈ th.allNodes) ∧
  (∀ m ∈ concreteMessages s, m.dst ∈ th.allNodes) ∧
  (∀ m ∈ concreteMessages s, m.dst = RingTheorems.nextNode m.src th)

noncomputable def abstractState (th : RingTheorems.Theory) (s : ConcreteState) :
    AbstractState th :=
  { leader := fun n => decide (n.val ∈ concreteLeader s)
    pending := fun sender dst =>
      decide (∃ m ∈ concreteMessages s, m.payload = sender.val ∧ m.dst = dst.val) }

def StateRel (th : RingTheorems.Theory) (sc : ConcreteState) (sa : AbstractState th) : Prop :=
  MessageInvariants th sc ∧
  (∀ sender dst : Node th,
    (∃ m ∈ concreteMessages sc, m.payload = sender.val ∧ m.dst = dst.val) →
      sa.pending sender dst = true)

def labelMatch (th : RingTheorems.Theory) :
    RingTheorems.Label → List (RingDec.Label (Node th)) → Prop
  | RingTheorems.Label.send, [RingDec.Label.send _ _] => True
  | RingTheorems.Label.recv, [RingDec.Label.recv _ _ _] => True
  | RingTheorems.Label.recv, [RingDec.Label.recv _ _ _, RingDec.Label.send _ _] => True
  | _, _ => False

theorem labelMatch_send (th : RingTheorems.Theory) (n next : Node th) :
    labelMatch th RingTheorems.Label.send [RingDec.Label.send n next] := by
  simp [labelMatch]

theorem labelMatch_recv (th : RingTheorems.Theory) (sender n next : Node th) :
    labelMatch th RingTheorems.Label.recv [RingDec.Label.recv sender n next] := by
  simp [labelMatch]

theorem labelMatch_recv_send (th : RingTheorems.Theory) (sender n next : Node th) :
    labelMatch th RingTheorems.Label.recv
      [RingDec.Label.recv sender n next, RingDec.Label.send sender next] := by
  simp [labelMatch]

noncomputable def setAbstractLeader {th : RingTheorems.Theory}
    (updates : FieldUpdateDescr [Node th] Bool)
    (leader : RingDec.FieldAbstractType (Node th) RingDec.State.Label.leader) :
    RingDec.FieldAbstractType (Node th) RingDec.State.Label.leader :=
  @FieldRepresentation.set [Node th] Bool
    (RingDec.FieldAbstractType (Node th) RingDec.State.Label.leader)
    (RingDec.instAbstractFieldRepresentation (Node th) RingDec.State.Label.leader)
    updates leader

noncomputable def setAbstractPending {th : RingTheorems.Theory}
    (updates : FieldUpdateDescr [Node th, Node th] Bool)
    (pending : RingDec.FieldAbstractType (Node th) RingDec.State.Label.pending) :
    RingDec.FieldAbstractType (Node th) RingDec.State.Label.pending :=
  @FieldRepresentation.set [Node th, Node th] Bool
    (RingDec.FieldAbstractType (Node th) RingDec.State.Label.pending)
    (RingDec.instAbstractFieldRepresentation (Node th) RingDec.State.Label.pending)
    updates pending

noncomputable def abstractSendPost {th : RingTheorems.Theory}
    (sa : AbstractState th) (sender dst : Node th) : AbstractState th := by
  classical
  exact
    { leader := sa.leader
      pending :=
        setAbstractPending
          ([((some sender, some dst, ()), fun _ _ => true)] :
            FieldUpdateDescr [Node th, Node th] Bool)
          sa.pending }

noncomputable def abstractRecvPost {th : RingTheorems.Theory}
    (sa : AbstractState th) (sender dst next : Node th) : AbstractState th := by
  classical
  exact
    if sender = dst then
      { leader :=
          setAbstractLeader
            ([((some dst, ()), fun _ => true)] : FieldUpdateDescr [Node th] Bool)
            sa.leader
        pending :=
          setAbstractPending
            ([((some sender, some dst, ()), fun _ _ => false)] :
              FieldUpdateDescr [Node th, Node th] Bool)
            sa.pending }
    else if TotalOrder.le dst sender then
      { leader := sa.leader
        pending :=
          setAbstractPending
            ([((some sender, some next, ()), fun _ _ => true),
              ((some sender, some dst, ()), fun _ _ => false)] :
              FieldUpdateDescr [Node th, Node th] Bool)
            sa.pending }
    else
      { leader := sa.leader
        pending :=
          setAbstractPending
            ([((some sender, some dst, ()), fun _ _ => false)] :
              FieldUpdateDescr [Node th, Node th] Bool)
            sa.pending }

theorem setAbstractPending_true_self {th : RingTheorems.Theory}
    (pending : RingDec.FieldAbstractType (Node th) RingDec.State.Label.pending)
    (sender dst : Node th) :
    setAbstractPending
        ([((some sender, some dst, ()), fun _ _ => true)] :
          FieldUpdateDescr [Node th, Node th] Bool)
        pending sender dst = true := by
  simp +unfoldPartialApp [setAbstractPending, FieldRepresentation.set,
    RingDec.instAbstractFieldRepresentation, CanonicalField.set,
    FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
    IteratedArrow.uncurry, IteratedProd.patCmp]

theorem setAbstractPending_true_of_ne {th : RingTheorems.Theory}
    (pending : RingDec.FieldAbstractType (Node th) RingDec.State.Label.pending)
    {sender dst sender' dst' : Node th}
    (hne : sender' ≠ sender ∨ dst' ≠ dst) :
    setAbstractPending
        ([((some sender, some dst, ()), fun _ _ => true)] :
          FieldUpdateDescr [Node th, Node th] Bool)
        pending sender' dst' = pending sender' dst' := by
  rcases hne with hne | hne
  · have hne' : sender ≠ sender' := fun h => hne h.symm
    simp +unfoldPartialApp [setAbstractPending, hne', FieldRepresentation.set,
      RingDec.instAbstractFieldRepresentation, CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
      IteratedArrow.uncurry, IteratedProd.patCmp]
  · have hne' : dst ≠ dst' := fun h => hne h.symm
    simp +unfoldPartialApp [setAbstractPending, hne', FieldRepresentation.set,
      RingDec.instAbstractFieldRepresentation, CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
      IteratedArrow.uncurry, IteratedProd.patCmp]

theorem setAbstractPending_true_mono {th : RingTheorems.Theory}
    (pending : RingDec.FieldAbstractType (Node th) RingDec.State.Label.pending)
    (sender dst sender' dst' : Node th)
    (h : pending sender' dst' = true) :
    setAbstractPending
        ([((some sender, some dst, ()), fun _ _ => true)] :
          FieldUpdateDescr [Node th, Node th] Bool)
        pending sender' dst' = true := by
  by_cases hsender : sender' = sender
  · by_cases hdst : dst' = dst
    · subst sender'
      subst dst'
      exact setAbstractPending_true_self pending sender dst
    · rw [setAbstractPending_true_of_ne pending (Or.inr hdst)]
      exact h
  · rw [setAbstractPending_true_of_ne pending (Or.inl hsender)]
    exact h

theorem setAbstractPending_false_of_ne {th : RingTheorems.Theory}
    (pending : RingDec.FieldAbstractType (Node th) RingDec.State.Label.pending)
    {sender dst sender' dst' : Node th}
    (hne : sender' ≠ sender ∨ dst' ≠ dst) :
    setAbstractPending
        ([((some sender, some dst, ()), fun _ _ => false)] :
          FieldUpdateDescr [Node th, Node th] Bool)
        pending sender' dst' = pending sender' dst' := by
  rcases hne with hne | hne
  · have hne' : sender ≠ sender' := fun h => hne h.symm
    simp +unfoldPartialApp [setAbstractPending, hne', FieldRepresentation.set,
      RingDec.instAbstractFieldRepresentation, CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
      IteratedArrow.uncurry, IteratedProd.patCmp]
  · have hne' : dst ≠ dst' := fun h => hne h.symm
    simp +unfoldPartialApp [setAbstractPending, hne', FieldRepresentation.set,
      RingDec.instAbstractFieldRepresentation, CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
    IteratedArrow.uncurry, IteratedProd.patCmp]

theorem setAbstractLeader_true_self {th : RingTheorems.Theory}
    (leader : RingDec.FieldAbstractType (Node th) RingDec.State.Label.leader)
    (n : Node th) :
    setAbstractLeader
        ([((some n, ()), fun _ => true)] : FieldUpdateDescr [Node th] Bool)
        leader n = true := by
  simp +unfoldPartialApp [setAbstractLeader, FieldRepresentation.set,
    RingDec.instAbstractFieldRepresentation, CanonicalField.set,
    FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
    IteratedArrow.uncurry, IteratedProd.patCmp]

theorem setAbstractLeader_true_mono {th : RingTheorems.Theory}
    (leader : RingDec.FieldAbstractType (Node th) RingDec.State.Label.leader)
    (n n' : Node th) (h : leader n' = true) :
    setAbstractLeader
        ([((some n, ()), fun _ => true)] : FieldUpdateDescr [Node th] Bool)
        leader n' = true := by
  by_cases hn : n' = n
  · subst n'
    exact setAbstractLeader_true_self leader n
  · have hn' : n ≠ n' := fun h => hn h.symm
    simp +unfoldPartialApp [setAbstractLeader, hn', h, FieldRepresentation.set,
      RingDec.instAbstractFieldRepresentation, CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
      IteratedArrow.uncurry, IteratedProd.patCmp]

theorem setAbstractPending_forward_self {th : RingTheorems.Theory}
    (pending : RingDec.FieldAbstractType (Node th) RingDec.State.Label.pending)
    (sender dst next : Node th) :
    setAbstractPending
        ([((some sender, some next, ()), fun _ _ => true),
          ((some sender, some dst, ()), fun _ _ => false)] :
          FieldUpdateDescr [Node th, Node th] Bool)
        pending sender next = true := by
  by_cases hnext_dst : next = dst
  · subst next
    simp +unfoldPartialApp [setAbstractPending, FieldRepresentation.set,
      RingDec.instAbstractFieldRepresentation, CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
      IteratedArrow.uncurry, IteratedProd.patCmp]
  · simp +unfoldPartialApp [setAbstractPending, FieldRepresentation.set,
      RingDec.instAbstractFieldRepresentation, CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
      IteratedArrow.uncurry, IteratedProd.patCmp]

theorem setAbstractPending_forward_of_ne {th : RingTheorems.Theory}
    (pending : RingDec.FieldAbstractType (Node th) RingDec.State.Label.pending)
    {sender dst next sender' dst' : Node th}
    (hneNew : sender' ≠ sender ∨ dst' ≠ next)
    (hneOld : sender' ≠ sender ∨ dst' ≠ dst) :
    setAbstractPending
        ([((some sender, some next, ()), fun _ _ => true),
          ((some sender, some dst, ()), fun _ _ => false)] :
          FieldUpdateDescr [Node th, Node th] Bool)
        pending sender' dst' = pending sender' dst' := by
  rcases hneNew with hneNew | hneNew <;> rcases hneOld with hneOld | hneOld
  · have hneNew' : sender ≠ sender' := fun h => hneNew h.symm
    simp +unfoldPartialApp [setAbstractPending, hneNew', FieldRepresentation.set,
      RingDec.instAbstractFieldRepresentation, CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
      IteratedArrow.uncurry, IteratedProd.patCmp]
  · have hneNew' : sender ≠ sender' := fun h => hneNew h.symm
    have hneOld' : dst ≠ dst' := fun h => hneOld h.symm
    simp +unfoldPartialApp [setAbstractPending, hneNew', hneOld', FieldRepresentation.set,
      RingDec.instAbstractFieldRepresentation, CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
      IteratedArrow.uncurry, IteratedProd.patCmp]
  · have hneNew' : next ≠ dst' := fun h => hneNew h.symm
    have hneOld' : sender ≠ sender' := fun h => hneOld h.symm
    simp +unfoldPartialApp [setAbstractPending, hneNew', hneOld', FieldRepresentation.set,
      RingDec.instAbstractFieldRepresentation, CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
      IteratedArrow.uncurry, IteratedProd.patCmp]
  · have hneNew' : next ≠ dst' := fun h => hneNew h.symm
    have hneOld' : dst ≠ dst' := fun h => hneOld h.symm
    simp +unfoldPartialApp [setAbstractPending, hneNew', hneOld', FieldRepresentation.set,
      RingDec.instAbstractFieldRepresentation, CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
      IteratedArrow.uncurry, IteratedProd.patCmp]

theorem stateRel_project {th : RingTheorems.Theory} {s : ConcreteState}
    (hinv : MessageInvariants th s) :
    StateRel th s (abstractState th s) := by
  constructor
  · exact hinv
  · intro sender dst hpending
    simp [abstractState]
    simpa [concreteMessages] using hpending

noncomputable def abstractNext (th : RingTheorems.Theory)
    (hass : RingTheorems.Assumptions RingTheorems.Theory th) (n : Node th) : Node th :=
  ⟨RingTheorems.nextNode n.val th, RingTheorems.nextNode_mem hass n.property⟩

theorem abstractNext_isNext (th : RingTheorems.Theory)
    (hass : RingTheorems.Assumptions RingTheorems.Theory th) (n : Node th) :
    ∀ Z : Node th,
      n ≠ abstractNext th hass n ∧
      (Z ≠ n ∧ Z ≠ abstractNext th hass n → Between.btw n (abstractNext th hass n) Z) := by
  intro Z
  constructor
  · intro h
    exact RingTheorems.nextNode_ne hass n.property (congrArg Subtype.val h)
  · intro hne
    rcases hass with ⟨hnodup, hnontriv⟩
    dsimp [abstractNext, Between.btw, nodeBetween, ordered_ring]
    have hn_idx : th.allNodes.idxOf n.val < th.allNodes.length :=
      List.idxOf_lt_length_iff.mpr n.property
    have hz_idx : th.allNodes.idxOf Z.val < th.allNodes.length :=
      List.idxOf_lt_length_iff.mpr Z.property
    have hnext_idx :=
      RingTheorems.idxOf_nextNode (th := th)
        (show RingTheorems.Assumptions RingTheorems.Theory th from ⟨hnodup, hnontriv⟩)
        n.property
    have hZ_ne_n_idx : th.allNodes.idxOf Z.val ≠ th.allNodes.idxOf n.val := by
      intro hidx
      exact hne.1 (Subtype.ext ((List.idxOf_inj Z.property).mp hidx))
    have hZ_ne_next_idx :
        th.allNodes.idxOf Z.val ≠ th.allNodes.idxOf (RingTheorems.nextNode n.val th) := by
      intro hidx
      exact hne.2 (Subtype.ext ((List.idxOf_inj Z.property).mp hidx))
    rw [hnext_idx] at hZ_ne_next_idx ⊢
    exact idxBtw_succ_of_ne hn_idx hz_idx hnontriv hZ_ne_n_idx hZ_ne_next_idx

theorem abstract_send_step {th : RingTheorems.Theory}
    (hass : RingTheorems.Assumptions RingTheorems.Theory th)
    (sa : AbstractState th) (n : Node th) :
    (abstractSystem th hass).tr RingDec.Theory.mk sa
      (RingDec.Label.send n (abstractNext th hass n))
      (abstractSendPost sa n (abstractNext th hass n)) := by
  letI := nodeInhabited th hass
  letI : (f : RingDec.State.Label) →
      FieldRepresentation (RingDec.State.Label.toDomain (Node th) f)
        (RingDec.State.Label.toCodomain (Node th) f)
        (RingDec.FieldAbstractType (Node th) f) :=
    RingDec.instAbstractFieldRepresentation (Node th)
  letI : (f : RingDec.State.Label) →
      LawfulFieldRepresentation (RingDec.State.Label.toDomain (Node th) f)
        (RingDec.State.Label.toCodomain (Node th) f)
        (RingDec.FieldAbstractType (Node th) f)
        (RingDec.instAbstractFieldRepresentation (Node th) f) :=
    RingDec.instLawfulAbstractFieldRepresentation (Node th)
  dsimp [abstractSystem, RingDec.relationalTransitionSystem, RingDec.Next]
  simp only [RingDec.NextAct, nextSimp]
  change RingDec.send.ext.tr (RingDec.Theory (Node th)) (AbstractState th) (Node th)
    (RingDec.FieldAbstractType (Node th)) n (abstractNext th hass n) RingDec.Theory.mk sa
      (abstractSendPost sa n (abstractNext th hass n))
  constructor
  · exact abstractNext_isNext th hass n
  · ext sender' dst' <;>
      simp [nextSimp, abstractSendPost, setAbstractPending]

theorem abstract_recv_step {th : RingTheorems.Theory}
    (hass : RingTheorems.Assumptions RingTheorems.Theory th)
    {sa : AbstractState th} {sender dst : Node th}
    (hpending : sa.pending sender dst = true) :
    (abstractSystem th hass).tr RingDec.Theory.mk sa
      (RingDec.Label.recv sender dst (abstractNext th hass dst))
      (abstractRecvPost sa sender dst (abstractNext th hass dst)) := by
  letI := nodeInhabited th hass
  letI : (f : RingDec.State.Label) →
      FieldRepresentation (RingDec.State.Label.toDomain (Node th) f)
        (RingDec.State.Label.toCodomain (Node th) f)
        (RingDec.FieldAbstractType (Node th) f) :=
    RingDec.instAbstractFieldRepresentation (Node th)
  letI : (f : RingDec.State.Label) →
      LawfulFieldRepresentation (RingDec.State.Label.toDomain (Node th) f)
        (RingDec.State.Label.toCodomain (Node th) f)
        (RingDec.FieldAbstractType (Node th) f)
        (RingDec.instAbstractFieldRepresentation (Node th) f) :=
    RingDec.instLawfulAbstractFieldRepresentation (Node th)
  dsimp [abstractSystem, RingDec.relationalTransitionSystem, RingDec.Next]
  simp only [RingDec.NextAct, nextSimp]
  change RingDec.recv.ext.tr (RingDec.Theory (Node th)) (AbstractState th) (Node th)
    (RingDec.FieldAbstractType (Node th)) sender dst (abstractNext th hass dst)
      RingDec.Theory.mk sa (abstractRecvPost sa sender dst (abstractNext th hass dst))
  constructor
  · exact abstractNext_isNext th hass dst
  constructor
  · exact hpending
  · by_cases hsender_dst : sender = dst
    · subst sender
      simp only [if_true]
      ext x y <;>
        simp [nextSimp, abstractRecvPost, setAbstractLeader, setAbstractPending]
    · simp only [hsender_dst, if_false]
      by_cases hle : TotalOrder.le dst sender
      · simp only [hle, if_true]
        ext x y <;>
          simp [nextSimp, abstractRecvPost, hsender_dst, hle, setAbstractPending]
      · simp only [hle, if_false]
        ext x y <;>
          simp [nextSimp, abstractRecvPost, hsender_dst, hle, setAbstractPending]

theorem messageInvariants_init {th : RingTheorems.Theory} {s : ConcreteState}
    (hinit : RingTheorems.relationalTransitionSystem.init th s) :
    MessageInvariants th s := by
  simp only [RingTheorems.relationalTransitionSystem, RingTheorems.Init, nextSimp] at hinit
  subst s
  simp +unfoldPartialApp [MessageInvariants, concreteMessages, FieldRepresentation.set,
    RingTheorems.instAbstractFieldRepresentation, CanonicalField.set,
    FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
    IteratedArrow.uncurry, IteratedProd.patCmp]

theorem messageInvariants_send {th : RingTheorems.Theory} {s s' : ConcreteState}
    (hass : RingTheorems.Assumptions RingTheorems.Theory th)
    (hinv : MessageInvariants th s)
    (htr : RingTheorems.relationalTransitionSystem.tr th s RingTheorems.Label.send s') :
    MessageInvariants th s' := by
  simp only [nextSimp] at htr
  rcases htr with ⟨n, hn, hstep⟩
  rcases hinv with ⟨hnodup, hpayload, hsrc, hdst, hshape⟩
  let msg : RingTheorems.Message :=
    { payload := n, src := n, dst := RingTheorems.nextNode n { allNodes := th.allNodes } }
  by_cases hmem : msg ∈ concreteMessages s
  · have hs : s = s' := by
      have hmem' : msg ∈ s.messages := by simpa [concreteMessages] using hmem
      simpa [msg, FieldRepresentation.get, RingTheorems.instAbstractFieldRepresentation, hmem'] using hstep
    subst s'
    exact ⟨hnodup, hpayload, hsrc, hdst, hshape⟩
  · have hs := by
      have hmem' : msg ∉ s.messages := by simpa [concreteMessages] using hmem
      simpa [msg, FieldRepresentation.get, RingTheorems.instAbstractFieldRepresentation, hmem'] using hstep
    subst s'
    have hnext_mem : RingTheorems.nextNode n { allNodes := th.allNodes } ∈ th.allNodes :=
      RingTheorems.nextNode_mem hass hn
    simp +unfoldPartialApp [MessageInvariants, concreteMessages, FieldRepresentation.set,
      CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
      IteratedArrow.uncurry, IteratedProd.patCmp, List.mem_insertOrdered]
    exact ⟨List.nodup_insertOrdered_of_not_mem hmem hnodup,
      ⟨hn, hpayload⟩, ⟨hn, hsrc⟩, ⟨hnext_mem, hdst⟩, hshape⟩

theorem messageInvariants_recv {th : RingTheorems.Theory} {s s' : ConcreteState}
    (hass : RingTheorems.Assumptions RingTheorems.Theory th)
    (hinv : MessageInvariants th s)
    (htr : RingTheorems.relationalTransitionSystem.tr th s RingTheorems.Label.recv s') :
    MessageInvariants th s' := by
  simp only [nextSimp] at htr
  rcases htr with ⟨m, hm, hstep⟩
  rcases hinv with ⟨hnodup, hpayload, hsrc, hdst, hshape⟩
  have hnodup_erase : (s.messages.erase m).Nodup := hnodup.erase m
  have hpayload_erase :
      ∀ msg ∈ s.messages.erase m, msg.payload ∈ th.allNodes := by
    intro msg hmsg
    exact hpayload msg (List.mem_of_mem_erase hmsg)
  have hsrc_erase :
      ∀ msg ∈ s.messages.erase m, msg.src ∈ th.allNodes := by
    intro msg hmsg
    exact hsrc msg (List.mem_of_mem_erase hmsg)
  have hdst_erase :
      ∀ msg ∈ s.messages.erase m, msg.dst ∈ th.allNodes := by
    intro msg hmsg
    exact hdst msg (List.mem_of_mem_erase hmsg)
  have hshape_erase :
      ∀ msg ∈ s.messages.erase m, msg.dst = RingTheorems.nextNode msg.src th := by
    intro msg hmsg
    exact hshape msg (List.mem_of_mem_erase hmsg)
  have hpayload_m : m.payload ∈ th.allNodes := hpayload m (by simpa [concreteMessages] using hm)
  have hdst_m : m.dst ∈ th.allNodes := hdst m (by simpa [concreteMessages] using hm)
  let msg : RingTheorems.Message :=
    { payload := m.payload, src := m.dst,
      dst := RingTheorems.nextNode m.dst { allNodes := th.allNodes } }
  by_cases hcond : m.payload = m.dst ∧ m.dst ∉ concreteLeader s
  · have hs := by
      have hcond' : m.payload = m.dst ∧ m.dst ∉ s.leader := by
        simpa [concreteLeader] using hcond
      simpa [concreteMessages, FieldRepresentation.get,
        RingTheorems.instAbstractFieldRepresentation, hcond'] using hstep
    subst s'
    simp +unfoldPartialApp [MessageInvariants, concreteMessages, FieldRepresentation.set,
      CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
      IteratedArrow.uncurry, IteratedProd.patCmp]
    exact ⟨hnodup_erase, hpayload_erase, hsrc_erase, hdst_erase, hshape_erase⟩
  · by_cases hle : m.dst ≤ m.payload
    · by_cases hmsg_mem : msg ∈ s.messages.erase m
      · have hs := by
          have hcond' : ¬(m.payload = m.dst ∧ m.dst ∉ s.leader) := by
            simpa [concreteLeader] using hcond
          simpa [msg, concreteMessages, FieldRepresentation.get,
            RingTheorems.instAbstractFieldRepresentation, hcond', hle, hmsg_mem] using hstep
        subst s'
        simp +unfoldPartialApp [MessageInvariants, concreteMessages, FieldRepresentation.set,
          CanonicalField.set,
          FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
          IteratedArrow.uncurry, IteratedProd.patCmp]
        exact ⟨hnodup_erase, hpayload_erase, hsrc_erase, hdst_erase, hshape_erase⟩
      · have hs := by
          have hcond' : ¬(m.payload = m.dst ∧ m.dst ∉ s.leader) := by
            simpa [concreteLeader] using hcond
          simpa [msg, concreteMessages, FieldRepresentation.get,
            RingTheorems.instAbstractFieldRepresentation, hcond', hle, hmsg_mem] using hstep
        subst s'
        have hnext_dst : RingTheorems.nextNode m.dst { allNodes := th.allNodes } ∈ th.allNodes :=
          RingTheorems.nextNode_mem hass hdst_m
        simp +unfoldPartialApp [MessageInvariants, concreteMessages, FieldRepresentation.set,
          CanonicalField.set,
          FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
          IteratedArrow.uncurry, IteratedProd.patCmp, List.mem_insertOrdered]
        exact ⟨List.nodup_insertOrdered_of_not_mem hmsg_mem hnodup_erase,
          ⟨hpayload_m, hpayload_erase⟩, ⟨hdst_m, hsrc_erase⟩, ⟨hnext_dst, hdst_erase⟩,
          hshape_erase⟩
    · have hs := by
        have hcond' : ¬(m.payload = m.dst ∧ m.dst ∉ s.leader) := by
          simpa [concreteLeader] using hcond
        simpa [concreteMessages, FieldRepresentation.get,
          RingTheorems.instAbstractFieldRepresentation, hcond', hle] using hstep
      subst s'
      simp +unfoldPartialApp [MessageInvariants, concreteMessages, FieldRepresentation.set,
        CanonicalField.set,
        FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
        IteratedArrow.uncurry, IteratedProd.patCmp]
      exact ⟨hnodup_erase, hpayload_erase, hsrc_erase, hdst_erase, hshape_erase⟩

theorem message_pair_unique {th : RingTheorems.Theory} {s : ConcreteState}
    (hass : RingTheorems.Assumptions RingTheorems.Theory th)
    (hinv : MessageInvariants th s)
    {m m' : RingTheorems.Message}
    (hm : m ∈ concreteMessages s) (hm' : m' ∈ concreteMessages s)
    (hpayload : m'.payload = m.payload) (hdst : m'.dst = m.dst) :
    m' = m := by
  rcases hinv with ⟨_, _, hsrc, _, hshape⟩
  have hsrc_m : m.src ∈ th.allNodes := hsrc m hm
  have hsrc_m' : m'.src ∈ th.allNodes := hsrc m' hm'
  have hnext_eq :
      RingTheorems.nextNode m'.src th = RingTheorems.nextNode m.src th := by
    rw [← hshape m' hm', ← hshape m hm, hdst]
  have hsrc_eq :=
    RingTheorems.nextNode_predecessor_unique hass hsrc_m' hsrc_m hnext_eq
  cases m
  cases m'
  simp_all

theorem erased_message_pair_ne {th : RingTheorems.Theory} {s : ConcreteState}
    (hass : RingTheorems.Assumptions RingTheorems.Theory th)
    (hinv : MessageInvariants th s)
    {m old : RingTheorems.Message}
    (hm : m ∈ concreteMessages s)
    (holdErase : old ∈ (concreteMessages s).erase m)
    (hpayload : old.payload = m.payload) (hdst : old.dst = m.dst) :
    False := by
  have hold : old ∈ concreteMessages s := List.mem_of_mem_erase holdErase
  have heq := message_pair_unique hass hinv hm hold hpayload hdst
  subst old
  exact hinv.1.not_mem_erase holdErase

theorem ring_refines (th : RingTheorems.Theory)
    (hass : RingTheorems.Assumptions RingTheorems.Theory th) :
    RelationalTransitionSystem.PointedTraceForwardSimulation
      RingTheorems.relationalTransitionSystem
      (abstractSystem th hass)
      th
      RingDec.Theory.mk
      (StateRel th)
      (labelMatch th) := by
  refine
    { assumptions := ?_
      init := ?_
      step := ?_ }
  · intro _
    simp [abstractSystem, RingDec.relationalTransitionSystem, RingDec.Assumptions]
  · intro sc _ hinit
    letI := nodeInhabited th hass
    refine ⟨abstractState th sc, ?_, stateRel_project (messageInvariants_init hinit)⟩
    have hinitConcrete := hinit
    simp only [RingTheorems.relationalTransitionSystem, RingTheorems.Init, nextSimp] at hinitConcrete
    subst sc
    simp +unfoldPartialApp [abstractSystem, abstractState, concreteLeader, concreteMessages,
      RingDec.relationalTransitionSystem, RingDec.Init, nextSimp, FieldRepresentation.set,
      RingDec.instAbstractFieldRepresentation, RingTheorems.instAbstractFieldRepresentation,
      CanonicalField.set,
      FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
      IteratedArrow.uncurry, IteratedProd.patCmp]
  · intro sc sc' sa label _ hrel htr
    cases label with
    | send =>
        rcases hrel with ⟨hinv, hpendingRel⟩
        have htrOriginal := htr
        simp only [nextSimp] at htr
        rcases htr with ⟨n, hn, hstep⟩
        let nNode : Node th := ⟨n, hn⟩
        let next : Node th := abstractNext th hass nNode
        let sa' : AbstractState th := abstractSendPost sa nNode next
        refine ⟨[RingDec.Label.send nNode next], sa',
          labelMatch_send th nNode next,
          RelationalTransitionSystem.multistep.single (abstract_send_step hass sa nNode), ?_⟩
        have hinv' : MessageInvariants th sc' :=
          messageInvariants_send hass hinv htrOriginal
        constructor
        · exact hinv'
        · intro sender dst hp
          let msg : RingTheorems.Message :=
            { payload := n, src := n,
              dst := RingTheorems.nextNode n { allNodes := th.allNodes } }
          by_cases hmem : msg ∈ concreteMessages sc
          · have hs : sc = sc' := by
              have hmem' : msg ∈ sc.messages := by simpa [concreteMessages] using hmem
              simpa [msg, FieldRepresentation.get, RingTheorems.instAbstractFieldRepresentation,
                hmem'] using hstep
            subst sc'
            simpa [sa', abstractSendPost] using
              setAbstractPending_true_mono sa.pending nNode next sender dst (hpendingRel sender dst hp)
          · have hs := by
              have hmem' : msg ∉ sc.messages := by simpa [concreteMessages] using hmem
              simpa [msg, FieldRepresentation.get, RingTheorems.instAbstractFieldRepresentation,
                hmem'] using hstep
            subst sc'
            rcases hp with ⟨m, hm, hpayload, hdst⟩
            have hm_cases : m = msg ∨ m ∈ concreteMessages sc := by
              simpa +unfoldPartialApp [msg, concreteMessages, FieldRepresentation.set,
                RingTheorems.instAbstractFieldRepresentation, CanonicalField.set,
                FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
                IteratedArrow.uncurry, IteratedProd.patCmp, List.mem_insertOrdered] using hm
            rcases hm_cases with rfl | hm_old
            · have hsender : sender = nNode := by
                apply Subtype.ext
                simpa [nNode, msg] using hpayload.symm
              have hdst' : dst = next := by
                apply Subtype.ext
                simpa [next, abstractNext, msg] using hdst.symm
              subst sender
              subst dst
              simpa [sa', abstractSendPost] using setAbstractPending_true_self sa.pending nNode next
            · have hold := hpendingRel sender dst ⟨m, hm_old, hpayload, hdst⟩
              simpa [sa', abstractSendPost] using
                setAbstractPending_true_mono sa.pending nNode next sender dst hold
    | recv =>
        rcases hrel with ⟨hinv, hpendingRel⟩
        have htrOriginal := htr
        simp only [nextSimp] at htr
        rcases htr with ⟨m, hm, hstep⟩
        let hmConcrete : m ∈ concreteMessages sc := by simpa [concreteMessages] using hm
        let sender : Node th := ⟨m.payload, hinv.2.1 m hmConcrete⟩
        let dst : Node th := ⟨m.dst, hinv.2.2.2.1 m hmConcrete⟩
        let next : Node th := abstractNext th hass dst
        have hpending : sa.pending sender dst = true :=
          hpendingRel sender dst ⟨m, hmConcrete, rfl, rfl⟩
        by_cases hself : sender = dst
        · have hpendingSelf : sa.pending dst dst = true := by
            simpa [hself] using hpending
          have hpayload_eq_dst : m.payload = m.dst := by
            have hvals := congrArg Subtype.val hself
            simpa [sender, dst] using hvals
          subst sender
          let recvPost : AbstractState th := abstractRecvPost sa dst dst next
          let finalPost : AbstractState th := abstractSendPost recvPost dst next
          refine ⟨[RingDec.Label.recv dst dst next, RingDec.Label.send dst next],
            finalPost, labelMatch_recv_send th dst dst next, ?_, ?_⟩
          · exact RelationalTransitionSystem.multistep.stepL
              (abstract_recv_step hass hpendingSelf)
              (RelationalTransitionSystem.multistep.single (by
                simpa [finalPost, recvPost] using abstract_send_step hass recvPost dst))
          · have hinv' : MessageInvariants th sc' :=
              messageInvariants_recv hass hinv htrOriginal
            constructor
            · exact hinv'
            intro sender' dst' hp
            let fmsg : RingTheorems.Message :=
              { payload := m.payload, src := m.dst,
                dst := RingTheorems.nextNode m.dst { allNodes := th.allNodes } }
            have oldCoverage :
                ∀ msg ∈ sc.messages.erase m,
                  msg.payload = sender'.val → msg.dst = dst'.val →
                    finalPost.pending sender' dst' = true := by
              intro msg hmsgErase hpayload hdst
              by_cases hnewSender : sender' = dst
              · by_cases hnewDst : dst' = next
                · subst sender'
                  subst dst'
                  simpa [finalPost, abstractSendPost] using
                    setAbstractPending_true_self recvPost.pending dst next
                · have hneNew : sender' ≠ dst ∨ dst' ≠ next := Or.inr hnewDst
                  have hneOld : sender' ≠ dst ∨ dst' ≠ dst := by
                    by_cases holdDst : dst' = dst
                    · exfalso
                      subst sender'
                      subst dst'
                      have hp : msg.payload = m.payload := by
                        simpa [dst, hpayload_eq_dst] using hpayload
                      have hd : msg.dst = m.dst := by
                        simpa [dst] using hdst
                      exact erased_message_pair_ne hass hinv hmConcrete hmsgErase hp hd
                    · exact Or.inr holdDst
                  have holdPending :=
                    hpendingRel sender' dst'
                      ⟨msg, List.mem_of_mem_erase hmsgErase, hpayload, hdst⟩
                  have hrecv : recvPost.pending sender' dst' = true := by
                    have hpres := setAbstractPending_false_of_ne sa.pending hneOld
                    dsimp [recvPost]
                    simp [abstractRecvPost]
                    rw [hpres]
                    exact holdPending
                  have hsend := setAbstractPending_true_of_ne recvPost.pending hneNew
                  simpa [finalPost, abstractSendPost, hsend] using hrecv
              · have hneNew : sender' ≠ dst ∨ dst' ≠ next := Or.inl hnewSender
                have hneOld : sender' ≠ dst ∨ dst' ≠ dst := Or.inl hnewSender
                have holdPending :=
                  hpendingRel sender' dst'
                    ⟨msg, List.mem_of_mem_erase hmsgErase, hpayload, hdst⟩
                have hrecv : recvPost.pending sender' dst' = true := by
                  have hpres := setAbstractPending_false_of_ne sa.pending hneOld
                  dsimp [recvPost]
                  simp [abstractRecvPost]
                  rw [hpres]
                  exact holdPending
                have hsend := setAbstractPending_true_of_ne recvPost.pending hneNew
                simpa [finalPost, abstractSendPost, hsend] using hrecv
            have forwardCoverage :
                ∀ msg, msg = fmsg → msg.payload = sender'.val → msg.dst = dst'.val →
                  finalPost.pending sender' dst' = true := by
              intro msg hmsg hpayload hdst
              subst msg
              have hsender' : sender' = dst := by
                apply Subtype.ext
                simpa [dst, fmsg, hpayload_eq_dst] using hpayload.symm
              have hdst' : dst' = next := by
                apply Subtype.ext
                simpa [next, abstractNext, fmsg] using hdst.symm
              subst sender'
              subst dst'
              simpa [finalPost, abstractSendPost] using
                setAbstractPending_true_self recvPost.pending dst next
            by_cases hcond : m.payload = m.dst ∧ m.dst ∉ concreteLeader sc
            · have hs := by
                have hcond' : m.payload = m.dst ∧ m.dst ∉ sc.leader := by
                  simpa [concreteLeader] using hcond
                simpa [concreteMessages, FieldRepresentation.get,
                  RingTheorems.instAbstractFieldRepresentation, hcond'] using hstep
              subst sc'
              rcases hp with ⟨msg, hmsg, hpayload, hdst⟩
              exact oldCoverage msg (by simpa [concreteMessages] using hmsg) hpayload hdst
            · have hle : m.dst ≤ m.payload := by omega
              by_cases hfmem : fmsg ∈ sc.messages.erase m
              · have hs := by
                  have hcond' : ¬(m.payload = m.dst ∧ m.dst ∉ sc.leader) := by
                    simpa [concreteLeader] using hcond
                  simpa [fmsg, concreteMessages, FieldRepresentation.get,
                    RingTheorems.instAbstractFieldRepresentation, hcond', hle, hfmem] using hstep
                subst sc'
                rcases hp with ⟨msg, hmsg, hpayload, hdst⟩
                exact oldCoverage msg (by simpa [concreteMessages] using hmsg) hpayload hdst
              · have hs := by
                  have hcond' : ¬(m.payload = m.dst ∧ m.dst ∉ sc.leader) := by
                    simpa [concreteLeader] using hcond
                  simpa [fmsg, concreteMessages, FieldRepresentation.get,
                    RingTheorems.instAbstractFieldRepresentation, hcond', hle, hfmem] using hstep
                subst sc'
                rcases hp with ⟨msg, hmsg, hpayload, hdst⟩
                have hcases : msg = fmsg ∨ msg ∈ sc.messages.erase m := by
                  simpa +unfoldPartialApp [fmsg, concreteMessages, FieldRepresentation.set,
                    RingTheorems.instAbstractFieldRepresentation, CanonicalField.set,
                    FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
                    IteratedArrow.uncurry, IteratedProd.patCmp, List.mem_insertOrdered] using hmsg
                rcases hcases with hmsgEq | hmsgOld
                · exact forwardCoverage msg hmsgEq hpayload hdst
                · exact oldCoverage msg hmsgOld hpayload hdst
        · let finalPost : AbstractState th := abstractRecvPost sa sender dst next
          refine ⟨[RingDec.Label.recv sender dst next], finalPost,
            labelMatch_recv th sender dst next,
            RelationalTransitionSystem.multistep.single (abstract_recv_step hass hpending), ?_⟩
          have hinv' : MessageInvariants th sc' :=
            messageInvariants_recv hass hinv htrOriginal
          constructor
          · exact hinv'
          intro sender' dst' hp
          have hpayload_ne_dst : m.payload ≠ m.dst := by
            intro hpayload_dst
            apply hself
            apply Subtype.ext
            simpa [sender, dst] using hpayload_dst
          have hcond : ¬(m.payload = m.dst ∧ m.dst ∉ concreteLeader sc) := by
            intro h
            exact hpayload_ne_dst h.1
          let fmsg : RingTheorems.Message :=
            { payload := m.payload, src := m.dst,
              dst := RingTheorems.nextNode m.dst { allNodes := th.allNodes } }
          by_cases hle : m.dst ≤ m.payload
          · have hleAbs : TotalOrder.le dst sender := by
              simpa [dst, sender, TotalOrder.le, nodeTotalOrder] using hle
            have oldCoverage :
                ∀ msg ∈ sc.messages.erase m,
                  msg.payload = sender'.val → msg.dst = dst'.val →
                    finalPost.pending sender' dst' = true := by
              intro msg hmsgErase hpayload hdst
              by_cases hnewSender : sender' = sender
              · by_cases hnewDst : dst' = next
                · subst sender'
                  subst dst'
                  simpa [finalPost, abstractRecvPost, hself, hleAbs] using
                    setAbstractPending_forward_self sa.pending sender dst next
                · have hneNew : sender' ≠ sender ∨ dst' ≠ next := Or.inr hnewDst
                  have hneOld : sender' ≠ sender ∨ dst' ≠ dst := by
                    by_cases holdDst : dst' = dst
                    · exfalso
                      subst sender'
                      subst dst'
                      have hp : msg.payload = m.payload := by
                        simpa [sender] using hpayload
                      have hd : msg.dst = m.dst := by
                        simpa [dst] using hdst
                      exact erased_message_pair_ne hass hinv hmConcrete hmsgErase hp hd
                    · exact Or.inr holdDst
                  have holdPending :=
                    hpendingRel sender' dst'
                      ⟨msg, List.mem_of_mem_erase hmsgErase, hpayload, hdst⟩
                  have hpres := setAbstractPending_forward_of_ne sa.pending hneNew hneOld
                  simpa [finalPost, abstractRecvPost, hself, hleAbs, hpres] using holdPending
              · have hneNew : sender' ≠ sender ∨ dst' ≠ next := Or.inl hnewSender
                have hneOld : sender' ≠ sender ∨ dst' ≠ dst := Or.inl hnewSender
                have holdPending :=
                  hpendingRel sender' dst'
                    ⟨msg, List.mem_of_mem_erase hmsgErase, hpayload, hdst⟩
                have hpres := setAbstractPending_forward_of_ne sa.pending hneNew hneOld
                simpa [finalPost, abstractRecvPost, hself, hleAbs, hpres] using holdPending
            have forwardCoverage :
                ∀ msg, msg = fmsg → msg.payload = sender'.val → msg.dst = dst'.val →
                  finalPost.pending sender' dst' = true := by
              intro msg hmsg hpayload hdst
              subst msg
              have hsender' : sender' = sender := by
                apply Subtype.ext
                simpa [sender, fmsg] using hpayload.symm
              have hdst' : dst' = next := by
                apply Subtype.ext
                simpa [next, abstractNext, fmsg] using hdst.symm
              subst sender'
              subst dst'
              simpa [finalPost, abstractRecvPost, hself, hleAbs] using
                setAbstractPending_forward_self sa.pending sender dst next
            by_cases hfmem : fmsg ∈ sc.messages.erase m
            · have hs := by
                have hcond' : ¬(m.payload = m.dst ∧ m.dst ∉ sc.leader) := by
                  simpa [concreteLeader] using hcond
                simpa [fmsg, concreteMessages, FieldRepresentation.get,
                  RingTheorems.instAbstractFieldRepresentation, hcond', hle, hfmem] using hstep
              subst sc'
              rcases hp with ⟨msg, hmsg, hpayload, hdst⟩
              exact oldCoverage msg (by simpa [concreteMessages] using hmsg) hpayload hdst
            · have hs := by
                have hcond' : ¬(m.payload = m.dst ∧ m.dst ∉ sc.leader) := by
                  simpa [concreteLeader] using hcond
                simpa [fmsg, concreteMessages, FieldRepresentation.get,
                  RingTheorems.instAbstractFieldRepresentation, hcond', hle, hfmem] using hstep
              subst sc'
              rcases hp with ⟨msg, hmsg, hpayload, hdst⟩
              have hcases : msg = fmsg ∨ msg ∈ sc.messages.erase m := by
                simpa +unfoldPartialApp [fmsg, concreteMessages, FieldRepresentation.set,
                  RingTheorems.instAbstractFieldRepresentation, CanonicalField.set,
                  FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
                  IteratedArrow.uncurry, IteratedProd.patCmp, List.mem_insertOrdered] using hmsg
              rcases hcases with hmsgEq | hmsgOld
              · exact forwardCoverage msg hmsgEq hpayload hdst
              · exact oldCoverage msg hmsgOld hpayload hdst
          · have hleAbs : ¬ TotalOrder.le dst sender := by
              simpa [dst, sender, TotalOrder.le, nodeTotalOrder] using hle
            have hs := by
              have hcond' : ¬(m.payload = m.dst ∧ m.dst ∉ sc.leader) := by
                simpa [concreteLeader] using hcond
              simpa [concreteMessages, FieldRepresentation.get,
                RingTheorems.instAbstractFieldRepresentation, hcond', hle] using hstep
            subst sc'
            rcases hp with ⟨msg, hmsg, hpayload, hdst⟩
            have hmsgErase : msg ∈ sc.messages.erase m := by
              simpa [concreteMessages] using hmsg
            by_cases holdSender : sender' = sender
            · by_cases holdDst : dst' = dst
              · subst sender'
                subst dst'
                have hp : msg.payload = m.payload := by
                  simpa [sender] using hpayload
                have hd : msg.dst = m.dst := by
                  simpa [dst] using hdst
                exact False.elim (erased_message_pair_ne hass hinv hmConcrete hmsgErase hp hd)
              · have holdPending :=
                  hpendingRel sender' dst'
                    ⟨msg, List.mem_of_mem_erase hmsgErase, hpayload, hdst⟩
                have hpres := setAbstractPending_false_of_ne (pending := sa.pending)
                  (sender := sender) (dst := dst) (sender' := sender') (dst' := dst')
                  (Or.inr holdDst)
                simpa [finalPost, abstractRecvPost, hself, hleAbs, hpres] using holdPending
            · have holdPending :=
                hpendingRel sender' dst'
                  ⟨msg, List.mem_of_mem_erase hmsgErase, hpayload, hdst⟩
              have hpres := setAbstractPending_false_of_ne (pending := sa.pending)
                (sender := sender) (dst := dst) (sender' := sender') (dst' := dst')
                (Or.inl holdSender)
              simpa [finalPost, abstractRecvPost, hself, hleAbs, hpres] using holdPending

end RingRefinement
