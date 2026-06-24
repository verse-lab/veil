import Mathlib.Data.List.Cycle
import Veil


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
invariant [leader_wf] ∀ L ∈ leader, L ∈ allNodes
invariant [msg_wf] ∀ m ∈ messages, m.payload ∈ allNodes ∧ m.src ∈ allNodes ∧ m.dst ∈ allNodes
invariant [leader_greatest] ∀ L ∈ leader, ∀ N ∈ allNodes, N ≤ L
invariant [self_msg_greatest] ∀ m ∈ messages, m.payload = m.dst → ∀ N ∈ allNodes, N ≤ m.payload
invariant [drop_smaller] ∀ m ∈ messages, ∀ N ∈ allNodes, btw m.payload N m.dst → N ≤ m.payload


set_option veil.solver "grind+smt"
set_option veil.smt.trust false
#gen_spec

/-! ## Ring-topology helper lemmas

The ghost relations `lt`/`btw` unfold to arithmetic on `List.idxOf`, and
`nextNode n { allNodes := L }` is `L.next n`. The following lemmas reduce
ring reasoning to modular arithmetic on indices. -/

theorem idxOf_lt_len {L : List Nat} {x : Nat} (h : x ∈ L) :
    List.idxOf x L < L.length :=
  List.idxOf_lt_length_of_mem h

theorem eq_of_idxOf_eq {L : List Nat} {x y : Nat} (hx : x ∈ L)
    (h : List.idxOf x L = List.idxOf y L) : x = y :=
  (List.idxOf_inj hx).mp h

/-- Node equality is equivalent to index equality, for members of `L`. -/
theorem eq_iff_idxOf {L : List Nat} {x y : Nat} (hx : x ∈ L) :
    x = y ↔ List.idxOf x L = List.idxOf y L :=
  (List.idxOf_inj hx).symm

theorem nextNode_eq_next {L : List Nat} {n : Nat} (hn : n ∈ L) :
    nextNode n { allNodes := L } = L.next n hn := by
  show (if h : n ∈ L then L.next n h else n) = L.next n hn
  rw [dif_pos hn]

theorem nextNode_mem {L : List Nat} {n : Nat} (hn : n ∈ L) :
    nextNode n { allNodes := L } ∈ L := by
  rw [nextNode_eq_next hn]; exact List.next_mem _ _ hn

theorem idxOf_nextNode {L : List Nat} (hL : L.Nodup) {n : Nat} (hn : n ∈ L) :
    List.idxOf (nextNode n { allNodes := L }) L = (List.idxOf n L + 1) % L.length := by
  rw [nextNode_eq_next hn, List.next_eq_getElem hn, hL.idxOf_getElem]

theorem nextNode_ne {L : List Nat} (hL : L.Nodup) (hlen : 1 < L.length) {n : Nat}
    (hn : n ∈ L) : nextNode n { allNodes := L } ≠ n := by
  intro h
  have e := idxOf_nextNode hL hn
  rw [h] at e
  have hb := idxOf_lt_len hn
  rcases Nat.lt_or_ge (List.idxOf n L + 1) L.length with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at e; omega
  · have : List.idxOf n L + 1 = L.length := by omega
    rw [this, Nat.mod_self] at e; omega

/-- The unfolded form of `btw a b c` (with `lt` expanded to `List.idxOf`),
exactly as it appears after `unveil`. -/
def btwIdx (L : List Nat) (a b c : Nat) : Prop :=
  (List.idxOf a L ≤ List.idxOf b L ∧ ¬ a = b) ∧
      List.idxOf b L ≤ List.idxOf c L ∧ ¬ b = c ∨
    (List.idxOf c L ≤ List.idxOf a L ∧ ¬ c = a) ∧
        List.idxOf a L ≤ List.idxOf b L ∧ ¬ a = b ∨
      (List.idxOf b L ≤ List.idxOf c L ∧ ¬ b = c) ∧
        List.idxOf c L ≤ List.idxOf a L ∧ ¬ c = a

/-- If `b` is (cyclically) between `a` and the successor of `d`, then either
`b = d` or `b` is between `a` and `d`. Used for the forwarding step. -/
theorem btw_pred {L : List Nat} (hL : L.Nodup) (hlen : 1 < L.length)
    {S N d : Nat} (hS : S ∈ L) (hN : N ∈ L) (hd : d ∈ L)
    (h : btwIdx L S N (nextNode d { allNodes := L })) :
    N = d ∨ btwIdx L S N d := by
  have hnd : nextNode d { allNodes := L } ∈ L := nextNode_mem hd
  have key := idxOf_nextNode hL hd
  have bSN := @eq_iff_idxOf L S N hS
  have bNd := @eq_iff_idxOf L N d hN
  have bdS := @eq_iff_idxOf L d S hd
  have bNnd := @eq_iff_idxOf L N (nextNode d { allNodes := L }) hN
  have bndS := @eq_iff_idxOf L (nextNode d { allNodes := L }) S hnd
  have hbS := idxOf_lt_len hS
  have hbN := idxOf_lt_len hN
  have hbd := idxOf_lt_len hd
  unfold btwIdx at h ⊢
  rcases Nat.lt_or_ge (List.idxOf d L + 1) L.length with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at key; omega
  · have he : List.idxOf d L + 1 = L.length := by omega
    rw [he, Nat.mod_self] at key; omega

/-- There is no node strictly between `n` and its successor. Used for the
`send` step, where the new message goes from `n` to `nextNode n`. -/
theorem btw_succ_false {L : List Nat} (hL : L.Nodup) (hlen : 1 < L.length)
    {n N : Nat} (hn : n ∈ L) (hN : N ∈ L) :
    ¬ btwIdx L n N (nextNode n { allNodes := L }) := by
  have hnn : nextNode n { allNodes := L } ∈ L := nextNode_mem hn
  have key := idxOf_nextNode hL hn
  have bnN := @eq_iff_idxOf L n N hn
  have bNnn := @eq_iff_idxOf L N (nextNode n { allNodes := L }) hN
  have bnnn := @eq_iff_idxOf L (nextNode n { allNodes := L }) n hnn
  have hbn := idxOf_lt_len hn
  have hbN := idxOf_lt_len hN
  unfold btwIdx
  rcases Nat.lt_or_ge (List.idxOf n L + 1) L.length with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at key; omega
  · have he : List.idxOf n L + 1 = L.length := by omega
    rw [he, Nat.mod_self] at key; omega

theorem mem_insertOrdered {a b : Message} {l : List Message} :
    a ∈ List.insertOrdered b l ↔ a = b ∨ a ∈ l :=
  List.mem_orderedInsert _

/-- If `S` is the successor of `d`, then every node `N` is `S`, `d`, or between
`S` and `d`. Used for the self-message step. -/
theorem ring_total {L : List Nat} (hL : L.Nodup) (_hlen : 1 < L.length)
    {S N d : Nat} (hS : S ∈ L) (hN : N ∈ L) (hd : d ∈ L)
    (hsd : S = nextNode d { allNodes := L }) :
    N = S ∨ N = d ∨ btwIdx L S N d := by
  have key := idxOf_nextNode hL hd
  rw [← hsd] at key
  have bNS := @eq_iff_idxOf L N S hN
  have bNd := @eq_iff_idxOf L N d hN
  have bSN := @eq_iff_idxOf L S N hS
  have bdS := @eq_iff_idxOf L d S hd
  have hbS := idxOf_lt_len hS
  have hbN := idxOf_lt_len hN
  have hbd := idxOf_lt_len hd
  unfold btwIdx
  rcases Nat.lt_or_ge (List.idxOf d L + 1) L.length with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at key; omega
  · have he : List.idxOf d L + 1 = L.length := by omega
    rw [he, Nat.mod_self] at key; omega

/-! ## Verification conditions

The proof obligations generated by `#check_invariants`, discharged manually
(the concrete model uses `List`/`Nat`, which is outside the SMT fragment). -/

section VCs

variable (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ]

@[veil]
theorem initializer_single_leader :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@initializer.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (fun _ _ => True) (@single_leader ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil

@[veil]
theorem initializer_leader_wf :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@initializer.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (fun _ _ => True) (@leader_wf ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil

@[veil]
theorem initializer_msg_wf :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@initializer.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (fun _ _ => True) (@msg_wf ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil

@[veil]
theorem initializer_leader_greatest :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@initializer.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (fun _ _ => True) (@leader_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil

@[veil]
theorem initializer_self_msg_greatest :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@initializer.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (fun _ _ => True) (@self_msg_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil

@[veil]
theorem initializer_drop_smaller :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@initializer.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (fun _ _ => True) (@drop_smaller ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil

-- `send` only ever appends the message `{ n, n, nextNode n }`; `leader` is untouched.

@[veil]
theorem send_single_leader :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@single_leader ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil
  intro hn
  exact hinv.1

@[veil]
theorem send_leader_wf :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@leader_wf ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil
  intro hn
  exact hinv.2.1

@[veil]
theorem send_msg_wf :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@msg_wf ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil
  intro hn
  have h_mwf := hinv.2.2.1
  split_ifs with hmsg
  · exact h_mwf
  · intro m hm
    rw [mem_insertOrdered] at hm
    rcases hm with rfl | hm
    · exact ⟨hn, hn, nextNode_mem hn⟩
    · exact h_mwf m hm

@[veil]
theorem send_leader_greatest :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@leader_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil
  intro hn
  exact hinv.2.2.2.1

@[veil]
theorem send_self_msg_greatest :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@self_msg_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil
  intro hn
  have h_smg := hinv.2.2.2.2.1
  split_ifs with hmsg
  · exact h_smg
  · intro m hm
    rw [mem_insertOrdered] at hm
    rcases hm with rfl | hm
    · intro hself
      exact absurd hself.symm (nextNode_ne has.1 has.2 hn)
    · exact h_smg m hm

@[veil]
theorem send_drop_smaller :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@drop_smaller ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil
  intro hn
  have h_ds := hinv.2.2.2.2.2
  split_ifs with hmsg
  · exact h_ds
  · intro m hm
    rw [mem_insertOrdered] at hm
    rcases hm with rfl | hm
    · intro N hN hbtw
      exact absurd hbtw (btw_succ_false has.1 has.2 hn hN)
    · exact h_ds m hm

-- `recv` erases `m`, may append the forwarded message `{ m.payload, m.dst, nextNode m.dst }`,
-- and in the become-leader branch prepends `m.dst` to `leader`.

@[veil]
theorem recv_single_leader :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@single_leader ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil
  intro hm
  split_ifs with hbecome
  · -- become leader: the existing leader must be empty
    obtain ⟨hpe, hnotin⟩ := hbecome
    rw [List.eq_nil_iff_forall_not_mem]
    intro L hL
    have hLin : L ∈ th.allNodes := hinv.2.1 L hL
    have hdin : m.dst ∈ th.allNodes := (hinv.2.2.1 m hm).2.2
    have h1 : m.dst ≤ L := hinv.2.2.2.1 L hL m.dst hdin
    have h2 : L ≤ m.dst := by
      have hle := hinv.2.2.2.2.1 m hm hpe L hLin
      rwa [hpe] at hle
    have : L = m.dst := le_antisymm h2 h1
    rw [this] at hL; exact hnotin hL
  · exact hinv.1

@[veil]
theorem recv_leader_wf :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@leader_wf ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil
  intro hm
  split_ifs with hbecome
  · exact ⟨(hinv.2.2.1 m hm).2.2, hinv.2.1⟩
  · exact hinv.2.1

@[veil]
theorem recv_leader_greatest :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@leader_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil
  intro hm
  split_ifs with hbecome
  · refine ⟨?_, hinv.2.2.2.1⟩
    obtain ⟨hpe, _⟩ := hbecome
    intro N hN
    have hle := hinv.2.2.2.2.1 m hm hpe N hN
    rwa [hpe] at hle
  · exact hinv.2.2.2.1

@[veil]
theorem recv_msg_wf :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@msg_wf ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil
  intro hm
  have h_mwf := hinv.2.2.1
  split_ifs with hbecome hfwd hpres
  · intro m₁ hm₁; exact h_mwf m₁ (List.mem_of_mem_erase hm₁)
  · intro m₁ hm₁; exact h_mwf m₁ (List.mem_of_mem_erase hm₁)
  · intro m₁ hm₁
    rw [mem_insertOrdered] at hm₁
    rcases hm₁ with rfl | hm₁
    · exact ⟨(h_mwf m hm).1, (h_mwf m hm).2.2, nextNode_mem (h_mwf m hm).2.2⟩
    · exact h_mwf m₁ (List.mem_of_mem_erase hm₁)
  · intro m₁ hm₁; exact h_mwf m₁ (List.mem_of_mem_erase hm₁)

@[veil]
theorem recv_self_msg_greatest :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@self_msg_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil
  intro hm
  have h_mwf := hinv.2.2.1
  have h_smg := hinv.2.2.2.2.1
  have h_ds := hinv.2.2.2.2.2
  split_ifs with hbecome hfwd hpres
  · intro m₁ hm₁; exact h_smg m₁ (List.mem_of_mem_erase hm₁)
  · intro m₁ hm₁; exact h_smg m₁ (List.mem_of_mem_erase hm₁)
  · intro m₁ hm₁
    rw [mem_insertOrdered] at hm₁
    rcases hm₁ with rfl | hm₁
    · intro hself N hN
      rcases ring_total (L := th.allNodes) (S := m.payload) (N := N) (d := m.dst)
          has.1 has.2 (h_mwf m hm).1 hN (h_mwf m hm).2.2 hself with hNS | hNd | hb
      · rw [hNS]
      · rw [hNd]; exact hfwd
      · exact h_ds m hm N hN hb
    · exact h_smg m₁ (List.mem_of_mem_erase hm₁)
  · intro m₁ hm₁; exact h_smg m₁ (List.mem_of_mem_erase hm₁)

@[veil]
theorem recv_drop_smaller :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@drop_smaller ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  unveil
  intro hm
  have h_mwf := hinv.2.2.1
  have h_ds := hinv.2.2.2.2.2
  split_ifs with hbecome hfwd hpres
  · intro m₁ hm₁ N hN hbtw; exact h_ds m₁ (List.mem_of_mem_erase hm₁) N hN hbtw
  · intro m₁ hm₁ N hN hbtw; exact h_ds m₁ (List.mem_of_mem_erase hm₁) N hN hbtw
  · intro m₁ hm₁
    rw [mem_insertOrdered] at hm₁
    rcases hm₁ with rfl | hm₁
    · intro N hN hbtw
      rcases btw_pred (L := th.allNodes) (S := m.payload) (N := N) (d := m.dst)
          has.1 has.2 (h_mwf m hm).1 hN (h_mwf m hm).2.2 hbtw with hNd | hb
      · rw [hNd]; exact hfwd
      · exact h_ds m hm N hN hb
    · intro N hN hbtw; exact h_ds m₁ (List.mem_of_mem_erase hm₁) N hN hbtw
  · intro m₁ hm₁ N hN hbtw; exact h_ds m₁ (List.mem_of_mem_erase hm₁) N hN hbtw

end VCs

#check_invariants

#gen_theorems

end RingTheorems
