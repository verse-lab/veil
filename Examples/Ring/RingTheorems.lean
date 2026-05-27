import Mathlib.Data.List.Cycle
import Veil

attribute [instance] leOfOrd

-- `sendToNext` uses `List.insertOrdered` as a set-like insert. These facts expose the
-- membership and `Nodup` behavior needed by the generated invariant goals.
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

-- The ring successor is determined by the cyclic order of `allNodes`. It is total so
-- the fallback outside the list is identity, but protocol proofs first establish membership.
private def List.cyclicNext (l : List Nat) (n : Nat) : Nat :=
  if h : n ∈ l then l.next n h else n

-- Private mirrors of the ghost relations let us prove reusable Lean lemmas before the
-- Veil module elaborates its module-scoped names.
private def ringLt (l : List Nat) (x y : Nat) : Prop :=
  l.idxOf x ≤ l.idxOf y ∧ x ≠ y

private def ringBtw (l : List Nat) (x y z : Nat) : Prop :=
  (ringLt l x y ∧ ringLt l y z) ∨
  (ringLt l z x ∧ ringLt l x y) ∨
  (ringLt l y z ∧ ringLt l z x)

private def idxBtw (x y z : Nat) : Prop :=
  (x < y ∧ y < z) ∨ (z < x ∧ x < y) ∨ (y < z ∧ z < x)

private theorem Nat.succ_mod_eq_zero_of_not_lt {i n : Nat} (hi : i < n)
    (hnot : ¬ i + 1 < n) :
    (i + 1) % n = 0 := by
  have hi_last : i + 1 = n := by omega
  rw [hi_last, Nat.mod_self]

-- Index-level arithmetic for stepping one position around a nontrivial cycle. These
-- lemmas are the arithmetic core behind the old axioms about `nextNode`.
private theorem Nat.succ_mod_ne_self_of_lt {i n : Nat} (hi : i < n) (hn : 1 < n) :
    (i + 1) % n ≠ i := by
  intro h
  by_cases hlt : i + 1 < n
  · have hmod : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt hlt
    omega
  · have hmod := Nat.succ_mod_eq_zero_of_not_lt hi hlt
    omega

-- No index is strictly between `s` and the immediate successor of `s`.
private theorem not_idxBtw_succ {len s n : Nat} (hs : s < len) (hn : n < len)
    (_hlen : 1 < len) :
    ¬ idxBtw s n ((s + 1) % len) := by
  intro hbtw
  by_cases hlt : s + 1 < len
  · have hnext : (s + 1) % len = s + 1 := Nat.mod_eq_of_lt hlt
    rcases hbtw with h | h | h
    all_goals
      simp [hnext] at h
      omega
  · have hnext := Nat.succ_mod_eq_zero_of_not_lt hs hlt
    rcases hbtw with h | h | h
    · simp [hnext] at h
    · simp [hnext] at h
      omega
    · simp [hnext] at h


-- If `n` is between `s` and the successor of `d`, then either `n` is `d` or it was
-- already between `s` and `d`.
private theorem idxBtw_extends_succ {len s n d : Nat}
    (_hs : s < len) (hn : n < len) (hd : d < len) (_hlen : 1 < len)
    (hbtw : idxBtw s n ((d + 1) % len)) :
    n = d ∨ idxBtw s n d := by
  by_cases hlt : d + 1 < len
  · have hnext : (d + 1) % len = d + 1 := Nat.mod_eq_of_lt hlt
    rcases hbtw with h | h | h
    all_goals
      by_cases hnd : n = d
      · exact Or.inl hnd
      · exact Or.inr (by simp [idxBtw, hnext] at h ⊢; omega)
  · have hnext := Nat.succ_mod_eq_zero_of_not_lt hd hlt
    rcases hbtw with h | h | h
    · simp [hnext] at h
    · by_cases hnd : n = d
      · exact Or.inl hnd
      · exact Or.inr (by simp [idxBtw, hnext] at h ⊢; omega)
    · simp [hnext] at h

private theorem idxBtw_closes_nonwrap {s n d : Nat} (hs : s = d + 1) :
    n = s ∨ n = d ∨ idxBtw s n d := by
  by_cases hns : n = s
  · exact Or.inl hns
  · by_cases hnd : n = d
    · exact Or.inr (Or.inl hnd)
    · by_cases hlt_nd : n < d
      · exact Or.inr (Or.inr (by simp [idxBtw, hs]; omega))
      · exact Or.inr (Or.inr (by simp [idxBtw, hs]; omega))

private theorem idxBtw_closes_wrap {len s n d : Nat}
    (hn : n < len) (hd_last : d + 1 = len) (hs : s = 0) :
    n = s ∨ n = d ∨ idxBtw s n d := by
  by_cases hns : n = s
  · exact Or.inl hns
  · by_cases hnd : n = d
    · exact Or.inr (Or.inl hnd)
    · exact Or.inr (Or.inr (by simp [idxBtw, hs]; omega))

-- If the successor of `d` wraps or advances exactly to `s`, every index is classified
-- as `s`, as `d`, or as lying between `s` and `d`.
private theorem idxBtw_closes_succ {len s n d : Nat}
    (hn : n < len) (hd : d < len) (_hlen : 1 < len)
    (hnext : (d + 1) % len = s) :
    n = s ∨ n = d ∨ idxBtw s n d := by
  by_cases hlt : d + 1 < len
  · have hmod : (d + 1) % len = d + 1 := Nat.mod_eq_of_lt hlt
    have hs : s = d + 1 := by omega
    exact idxBtw_closes_nonwrap hs
  · have hd_last : d + 1 = len := by omega
    have hmod := Nat.succ_mod_eq_zero_of_not_lt hd hlt
    have hs : s = 0 := by omega
    exact idxBtw_closes_wrap hn hd_last hs

-- Convert between the ghost-style ring relations and strict arithmetic facts about
-- `idxOf`. `Nodup` is what turns unequal list elements into unequal indices.
private theorem idx_lt_of_ringLt {l : List Nat} (_hnodup : l.Nodup) {x y : Nat}
    (hx : x ∈ l) (hxy : ringLt l x y) :
    l.idxOf x < l.idxOf y := by
  have hne : l.idxOf x ≠ l.idxOf y := by
    intro hidx
    exact hxy.2 ((List.idxOf_inj hx).mp hidx)
  exact Nat.lt_of_le_of_ne hxy.1 hne

private theorem ringLt_of_idx_lt {l : List Nat} {x y : Nat}
    (hxy : l.idxOf x < l.idxOf y) :
    ringLt l x y := by
  constructor
  · omega
  · intro h
    subst y
    omega

private theorem idxBtw_of_ringBtw {l : List Nat} (hnodup : l.Nodup)
    {x y z : Nat} (hx : x ∈ l) (hy : y ∈ l) (hz : z ∈ l)
    (hbtw : ringBtw l x y z) :
    idxBtw (l.idxOf x) (l.idxOf y) (l.idxOf z) := by
  rcases hbtw with h | h | h
  · exact Or.inl ⟨idx_lt_of_ringLt hnodup hx h.1, idx_lt_of_ringLt hnodup hy h.2⟩
  · exact Or.inr (Or.inl ⟨idx_lt_of_ringLt hnodup hz h.1, idx_lt_of_ringLt hnodup hx h.2⟩)
  · exact Or.inr (Or.inr ⟨idx_lt_of_ringLt hnodup hy h.1, idx_lt_of_ringLt hnodup hz h.2⟩)

private theorem ringBtw_of_idxBtw {l : List Nat} {x y z : Nat}
    (hbtw : idxBtw (l.idxOf x) (l.idxOf y) (l.idxOf z)) :
    ringBtw l x y z := by
  rcases hbtw with h | h | h
  · exact Or.inl ⟨ringLt_of_idx_lt h.1, ringLt_of_idx_lt h.2⟩
  · exact Or.inr (Or.inl ⟨ringLt_of_idx_lt h.1, ringLt_of_idx_lt h.2⟩)
  · exact Or.inr (Or.inr ⟨ringLt_of_idx_lt h.1, ringLt_of_idx_lt h.2⟩)

-- Basic facts about `cyclicNext`: it agrees with Mathlib's `List.next`, preserves
-- membership, advances `idxOf` modulo the length, and is never a self-loop when the
-- cycle has at least two distinct elements.
private theorem List.cyclicNext_of_mem {l : List Nat} {n : Nat} (hn : n ∈ l) :
    l.cyclicNext n = l.next n hn := by
  simp [List.cyclicNext, hn]

private theorem List.cyclicNext_mem {l : List Nat} {n : Nat} (hn : n ∈ l) :
    l.cyclicNext n ∈ l := by
  simp [List.cyclicNext, hn]
  exact List.next_mem l n hn

private theorem List.idxOf_cyclicNext {l : List Nat} (hnodup : l.Nodup) {n : Nat} (hn : n ∈ l) :
    l.idxOf (l.cyclicNext n) = (l.idxOf n + 1) % l.length := by
  rw [List.cyclicNext_of_mem hn, List.next_eq_getElem hn]
  exact hnodup.idxOf_getElem _ _

private theorem List.cyclicNext_ne {l : List Nat} (hnodup : l.Nodup) (hlen : 1 < l.length)
    {n : Nat} (hn : n ∈ l) :
    n ≠ l.cyclicNext n := by
  intro heq
  have hidx := List.idxOf_cyclicNext hnodup hn
  have hs : l.idxOf (l.cyclicNext n) = l.idxOf n := by rw [← heq]
  rw [hidx] at hs
  exact Nat.succ_mod_ne_self_of_lt (List.idxOf_lt_length_iff.mpr hn) hlen hs

-- Recover the former `nextNode_no_between` assumption from the list-derived successor.
private theorem ringBtw_no_cyclicNext {l : List Nat} (hnodup : l.Nodup) (hlen : 1 < l.length)
    {s n : Nat} (hs : s ∈ l) (hn : n ∈ l) :
    ¬ ringBtw l s n (l.cyclicNext s) := by
  intro hbtw
  have hnext_mem : l.cyclicNext s ∈ l := List.cyclicNext_mem hs
  have hidxBtw := idxBtw_of_ringBtw hnodup hs hn hnext_mem hbtw
  have hidxNext := List.idxOf_cyclicNext hnodup hs
  exact not_idxBtw_succ (List.idxOf_lt_length_iff.mpr hs) (List.idxOf_lt_length_iff.mpr hn) hlen
    (by simpa [hidxNext] using hidxBtw)

-- Recover the former `nextNode_extends_between` assumption by translating to indices,
-- pulling the upper endpoint back from `cyclicNext d` to `d`, then translating back.
private theorem ringBtw_extends_cyclicNext {l : List Nat} (hnodup : l.Nodup) (hlen : 1 < l.length)
    {s d n : Nat} (hs : s ∈ l) (hd : d ∈ l) (hn : n ∈ l)
    (hbtw : ringBtw l s n (l.cyclicNext d)) :
    n = d ∨ ringBtw l s n d := by
  have hnext_mem : l.cyclicNext d ∈ l := List.cyclicNext_mem hd
  have hidxBtw := idxBtw_of_ringBtw hnodup hs hn hnext_mem hbtw
  have hidxNext := List.idxOf_cyclicNext hnodup hd
  have hcases := idxBtw_extends_succ
    (List.idxOf_lt_length_iff.mpr hs) (List.idxOf_lt_length_iff.mpr hn)
    (List.idxOf_lt_length_iff.mpr hd) hlen (by simpa [hidxNext] using hidxBtw)
  rcases hcases with hnd | hidx
  · exact Or.inl ((List.idxOf_inj hn).mp hnd)
  · exact Or.inr (ringBtw_of_idxBtw hidx)

-- Recover the former `nextNode_closes_between` assumption for the case where `d`'s
-- successor is `s`.
private theorem ringBtw_closes_cyclicNext {l : List Nat} (hnodup : l.Nodup) (hlen : 1 < l.length)
    {s d n : Nat} (_hs : s ∈ l) (hd : d ∈ l) (hn : n ∈ l)
    (hnext : l.cyclicNext d = s) :
    n = s ∨ n = d ∨ ringBtw l s n d := by
  have hidxNext := List.idxOf_cyclicNext hnodup hd
  have hidxEq : (l.idxOf d + 1) % l.length = l.idxOf s := by
    rw [← hidxNext, hnext]
  have hcases := idxBtw_closes_succ (List.idxOf_lt_length_iff.mpr hn)
    (List.idxOf_lt_length_iff.mpr hd) hlen hidxEq
  rcases hcases with hns | hrest
  · exact Or.inl ((List.idxOf_inj hn).mp hns)
  · rcases hrest with hnd | hidx
    · exact Or.inr (Or.inl ((List.idxOf_inj hn).mp hnd))
    · exact Or.inr (Or.inr (ringBtw_of_idxBtw hidx))

veil module RingTheorems

immutable individual allNodes : List Nat

individual leader : List Nat

@[veil_decl] structure Message where
  payload : Nat
  src : Nat
  dst : Nat

individual messages : List Message

#gen_state

theory ghost function nextNode (n : Nat) : Nat :=
  if h : n ∈ allNodes then allNodes.next n h else n

theory ghost relation lt (x y : Nat) := allNodes.idxOf x ≤ allNodes.idxOf y ∧ x ≠ y

theory ghost relation btw (x y z : Nat) :=
  (lt x y ∧ lt y z) ∨ (lt z x ∧ lt x y) ∨ (lt y z ∧ lt z x)

theory ghost relation isNext (n : Nat) (next : Nat) :=
  n ∈ allNodes ∧ next ∈ allNodes ∧ n ≠ next ∧
  ∀ Z ∈ allNodes, Z ≠ n ∧ Z ≠ next → btw n next Z

assumption [allNodes_nodup] allNodes.Nodup
assumption [allNodes_nontrivial] 1 < allNodes.length

after_init {
  leader := []
  messages := []
}

procedure sendToNext (payload src : Nat) {
  let msg := Message.mk payload src (nextNode src)
  if msg ∉ messages then
    messages := messages.insertOrdered msg
}

action send {
  let n :| n ∈ allNodes
  sendToNext n n
}

action recv {
  let m :| m ∈ messages
  let n := m.dst
  messages := messages.erase m
  if m.payload = n && n ∉ leader then
    leader := n :: leader
  else
    if n ≤ m.payload then
      sendToNext m.payload n
}

safety [single_leader] leader.length ≤ 1
invariant [leader_nodup] leader.Nodup
invariant [messages_nodup] messages.Nodup
invariant [leader_in_allNodes] ∀ L ∈ leader, L ∈ allNodes
invariant [messages_payload_in_allNodes] ∀ m ∈ messages, m.payload ∈ allNodes
invariant [messages_src_in_allNodes] ∀ m ∈ messages, m.src ∈ allNodes
invariant [messages_dst_in_allNodes] ∀ m ∈ messages, m.dst ∈ allNodes
invariant [leader_greatest] ∀ L ∈ leader, ∀ N ∈ allNodes, N ≤ L
invariant [self_msg_greatest] ∀ m ∈ messages, m.payload = m.dst → ∀ N ∈ allNodes, N ≤ m.payload
invariant [drop_smaller] ∀ m ∈ messages, ∀ N ∈ allNodes, btw m.payload N m.dst → N ≤ m.payload

set_option veil.solver "grind+smt"

#gen_spec

@[veil]
theorem send_messages_nodup (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@messages_nodup ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro ht
  rcases hinv with ⟨_, _, hmessages_nodup, _⟩
  let msg : Message := { payload := n, src := n, dst := nextNode n th }
  by_cases hmem : msg ∈ st.messages
  · simpa [msg, hmem] using hmessages_nodup
  · simp [msg, hmem]
    exact (List.perm_orderedInsert
      (r := fun x y : Message => compare x y == Ordering.lt)
      msg st.messages).nodup_iff.mpr (List.Nodup.cons hmem hmessages_nodup)

@[veil]
theorem send_messages_payload_in_allNodes (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@messages_payload_in_allNodes ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro ht
  rcases hinv with ⟨_, _, _, _, hpayload, _⟩
  let msg : Message := { payload := n, src := n, dst := nextNode n th }
  by_cases hmem : msg ∈ st.messages
  · simpa [msg, hmem] using hpayload
  · simp [msg, hmem, List.mem_insertOrdered]
    exact ⟨ht, hpayload⟩

@[veil]
theorem send_messages_src_in_allNodes (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@messages_src_in_allNodes ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro ht
  rcases hinv with ⟨_, _, _, _, _, hsrc, _⟩
  let msg : Message := { payload := n, src := n, dst := nextNode n th }
  by_cases hmem : msg ∈ st.messages
  · simpa [msg, hmem] using hsrc
  · simp [msg, hmem, List.mem_insertOrdered]
    exact ⟨ht, hsrc⟩

@[veil]
theorem send_messages_dst_in_allNodes (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@messages_dst_in_allNodes ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro ht
  rcases has with ⟨_hnodup, _hnontriv⟩
  rcases hinv with ⟨_, _, _, _, _, _, hdst, _⟩
  have hnext_mem : nextNode n th ∈ th.allNodes := by
    simpa [nextNode] using List.cyclicNext_mem (l := th.allNodes) ht
  let msg : Message := { payload := n, src := n, dst := nextNode n th }
  by_cases hmem : msg ∈ st.messages
  · simpa [msg, hmem] using hdst
  · simp [msg, hmem, List.mem_insertOrdered]
    exact ⟨hnext_mem, hdst⟩

@[veil]
theorem send_self_msg_greatest (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@self_msg_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro ht
  rcases has with ⟨hnodup, hnontriv⟩
  rcases hinv with ⟨_, _, _, _, _, _, _, _, hself, _⟩
  have hnext_ne : ∀ h : n ∈ th.allNodes, n ≠ th.allNodes.next n h := by
    intro h
    have hcyclic := List.cyclicNext_ne (l := th.allNodes) hnodup hnontriv h
    simpa [List.cyclicNext, h] using hcyclic
  let msg : Message := { payload := n, src := n, dst := nextNode n th }
  by_cases hmem : msg ∈ st.messages
  · simpa [msg, hmem] using hself
  · simp [msg, hmem, List.mem_insertOrdered]
    exact ⟨fun heq _ _ => False.elim (hnext_ne ht (heq ht)), hself⟩

@[veil]
theorem send_drop_smaller (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@drop_smaller ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro ht
  rcases has with ⟨hnodup, hnontriv⟩
  rcases hinv with ⟨_, _, _, _, _, _, _, _, _, hdrop⟩
  let msg : Message := { payload := n, src := n, dst := nextNode n th }
  by_cases hmem : msg ∈ st.messages
  · simpa [msg, hmem] using hdrop
  · simp [msg, hmem, List.mem_insertOrdered]
    exact ⟨fun N hN hbtw =>
      False.elim <| ringBtw_no_cyclicNext hnodup hnontriv ht hN
        (by simpa [nextNode, List.cyclicNext, ht, ringBtw, ringLt] using hbtw), hdrop⟩

@[veil]
theorem recv_single_leader (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@single_leader ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro ht
  rcases hinv with
    ⟨hsingle, _, _, hleader_mem, hpayload, _, _, hleader_greatest, hself, _⟩
  by_cases hcond : m.payload = m.dst ∧ m.dst ∉ st.leader
  · rcases hcond with ⟨hp_eq_dst, hnot_leader⟩
    cases st.leader with
    | nil =>
      simp [hp_eq_dst]
    | cons L tail =>
      exfalso
      have hLmem : L ∈ L :: tail := by simp
      have hL_nodes : L ∈ th.allNodes := hleader_mem L hLmem
      have hp_nodes : m.payload ∈ th.allNodes := hpayload m ht
      have hL_le_payload : L ≤ m.payload := hself m ht hp_eq_dst L hL_nodes
      have hp_le_L : m.payload ≤ L := hleader_greatest L hLmem m.payload hp_nodes
      have hL_eq_payload : L = m.payload := Nat.le_antisymm hL_le_payload hp_le_L
      apply hnot_leader
      have hL_eq_dst : L = m.dst := hL_eq_payload.trans hp_eq_dst
      simp [hL_eq_dst]
  · simpa [hcond] using hsingle

@[veil]
theorem recv_messages_nodup (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@messages_nodup ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro ht
  rcases hinv with ⟨_, _, hmessages_nodup, _⟩
  have hmessages_erase_nodup : (st.messages.erase m).Nodup := hmessages_nodup.erase m
  let msg : Message := { payload := m.payload, src := m.dst, dst := nextNode m.dst th }
  by_cases hcond : m.payload = m.dst ∧ m.dst ∉ st.leader
  · simpa [hcond] using hmessages_erase_nodup
  · by_cases hle : m.dst ≤ m.payload
    · by_cases hmem : msg ∈ st.messages.erase m
      · simpa [hcond, hle, msg, hmem] using hmessages_erase_nodup
      · simp [hcond, hle, msg, hmem]
        exact List.nodup_insertOrdered_of_not_mem hmem hmessages_erase_nodup
    · simpa [hcond, hle] using hmessages_erase_nodup

@[veil]
theorem recv_messages_payload_in_allNodes (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@messages_payload_in_allNodes ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro ht
  rcases hinv with ⟨_, _, _, _, hpayload, _⟩
  have hpayload_erase : ∀ msg' ∈ st.messages.erase m, msg'.payload ∈ th.allNodes := by
    intro msg' hm
    exact hpayload msg' (List.mem_of_mem_erase hm)
  have hpayload_m : m.payload ∈ th.allNodes := hpayload m ht
  let msg : Message := { payload := m.payload, src := m.dst, dst := nextNode m.dst th }
  by_cases hcond : m.payload = m.dst ∧ m.dst ∉ st.leader
  · simpa [hcond] using hpayload_erase
  · by_cases hle : m.dst ≤ m.payload
    · by_cases hmem : msg ∈ st.messages.erase m
      · simpa [hcond, hle, msg, hmem] using hpayload_erase
      · simp [hcond, hle, msg, hmem, List.mem_insertOrdered]
        exact ⟨hpayload_m, hpayload_erase⟩
    · simpa [hcond, hle] using hpayload_erase

@[veil]
theorem recv_messages_src_in_allNodes (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@messages_src_in_allNodes ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro ht
  rcases hinv with ⟨_, _, _, _, _, hsrc, hdst, _⟩
  have hsrc_erase : ∀ msg' ∈ st.messages.erase m, msg'.src ∈ th.allNodes := by
    intro msg' hm
    exact hsrc msg' (List.mem_of_mem_erase hm)
  have hdst_m : m.dst ∈ th.allNodes := hdst m ht
  let msg : Message := { payload := m.payload, src := m.dst, dst := nextNode m.dst th }
  by_cases hcond : m.payload = m.dst ∧ m.dst ∉ st.leader
  · simpa [hcond] using hsrc_erase
  · by_cases hle : m.dst ≤ m.payload
    · by_cases hmem : msg ∈ st.messages.erase m
      · simpa [hcond, hle, msg, hmem] using hsrc_erase
      · simp [hcond, hle, msg, hmem, List.mem_insertOrdered]
        exact ⟨hdst_m, hsrc_erase⟩
    · simpa [hcond, hle] using hsrc_erase

@[veil]
theorem recv_messages_dst_in_allNodes (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@messages_dst_in_allNodes ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro ht
  rcases has with ⟨_hnodup, _hnontriv⟩
  rcases hinv with ⟨_, _, _, _, _, _, hdst, _⟩
  have hdst_erase : ∀ msg' ∈ st.messages.erase m, msg'.dst ∈ th.allNodes := by
    intro msg' hm
    exact hdst msg' (List.mem_of_mem_erase hm)
  have hdst_m : m.dst ∈ th.allNodes := hdst m ht
  have hnext_dst : nextNode m.dst th ∈ th.allNodes := by
    simpa [nextNode] using List.cyclicNext_mem (l := th.allNodes) hdst_m
  let msg : Message := { payload := m.payload, src := m.dst, dst := nextNode m.dst th }
  by_cases hcond : m.payload = m.dst ∧ m.dst ∉ st.leader
  · simpa [hcond] using hdst_erase
  · by_cases hle : m.dst ≤ m.payload
    · by_cases hmem : msg ∈ st.messages.erase m
      · simpa [hcond, hle, msg, hmem] using hdst_erase
      · simp [hcond, hle, msg, hmem, List.mem_insertOrdered]
        exact ⟨hnext_dst, hdst_erase⟩
    · simpa [hcond, hle] using hdst_erase

@[veil]
theorem recv_self_msg_greatest (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@self_msg_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro ht
  rcases has with ⟨hnodup, hnontriv⟩
  rcases hinv with ⟨_, _, _, _, hpayload, _, hdst, _, hself, hdrop⟩
  have hself_erase :
      ∀ msg' ∈ st.messages.erase m, msg'.payload = msg'.dst → ∀ N ∈ th.allNodes, N ≤ msg'.payload := by
    intro msg' hm
    exact hself msg' (List.mem_of_mem_erase hm)
  have hpayload_m : m.payload ∈ th.allNodes := hpayload m ht
  have hdst_m : m.dst ∈ th.allNodes := hdst m ht
  let msg : Message := { payload := m.payload, src := m.dst, dst := nextNode m.dst th }
  by_cases hcond : m.payload = m.dst ∧ m.dst ∉ st.leader
  · simpa [hcond] using hself_erase
  · by_cases hle : m.dst ≤ m.payload
    · by_cases hmem : msg ∈ st.messages.erase m
      · simpa [hcond, hle, msg, hmem] using hself_erase
      · have hnew_self :
            m.payload = nextNode m.dst th → ∀ N ∈ th.allNodes, N ≤ m.payload := by
          intro hmsg_self N hN
          have hcases := ringBtw_closes_cyclicNext hnodup hnontriv hpayload_m hdst_m hN
            (by simpa [nextNode] using hmsg_self.symm)
          rcases hcases with hN_payload | hrest
          · simp [hN_payload]
          · rcases hrest with hN_dst | hbtw
            · simp [hN_dst, hle]
            · exact hdrop m ht N hN hbtw
        simp [hcond, hle, msg, hmem, List.mem_insertOrdered]
        exact ⟨hnew_self, hself_erase⟩
    · simpa [hcond, hle] using hself_erase

@[veil]
theorem recv_drop_smaller (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@drop_smaller ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro ht
  rcases has with ⟨hnodup, hnontriv⟩
  rcases hinv with ⟨_, _, _, _, hpayload, _, hdst, _, _, hdrop⟩
  have hpayload_m : m.payload ∈ th.allNodes := hpayload m ht
  have hdst_m : m.dst ∈ th.allNodes := hdst m ht
  let msg : Message := { payload := m.payload, src := m.dst, dst := nextNode m.dst th }
  by_cases hcond : m.payload = m.dst ∧ m.dst ∉ st.leader
  · simp [hcond]
    intro msg' hm N hN hbtw
    exact hdrop msg' (List.mem_of_mem_erase (b := m) hm) N hN hbtw
  · by_cases hle : m.dst ≤ m.payload
    · by_cases hmem : msg ∈ st.messages.erase m
      · simp [hcond, hle, msg, hmem]
        intro msg' hm N hN hbtw
        exact hdrop msg' (List.mem_of_mem_erase (b := m) hm) N hN hbtw
      · simp [hcond, hle, msg, hmem, List.mem_insertOrdered]
        constructor
        · intro N hN hbtw
          have hcases := ringBtw_extends_cyclicNext hnodup hnontriv hpayload_m hdst_m hN
            (by simpa [nextNode, ringBtw, ringLt] using hbtw)
          rcases hcases with hN_dst | hbtw_old
          · simp [hN_dst, hle]
          · exact hdrop m ht N hN hbtw_old
        · intro msg' hm N hN hbtw
          exact hdrop msg' (List.mem_of_mem_erase (b := m) hm) N hN hbtw
    · simp [hcond, hle]
      intro msg' hm N hN hbtw
      exact hdrop msg' (List.mem_of_mem_erase (b := m) hm) N hN hbtw

#check_invariants

#model_check { }
  { allNodes := [1, 5, 2, 4, 3] }

end RingTheorems
