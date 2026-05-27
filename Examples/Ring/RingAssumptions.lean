import Veil

attribute [instance] leOfOrd

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

veil module RingOne

immutable individual allNodes : List Nat
immutable function nextNode : Nat → Nat

individual leader : List Nat

@[veil_decl] structure Message where
  payload : Nat
  src : Nat
  dst : Nat

individual messages : List Message

#gen_state

theory ghost relation lt (x y : Nat) := allNodes.idxOf x ≤ allNodes.idxOf y ∧ x ≠ y

theory ghost relation btw (x y z : Nat) :=
  (lt x y ∧ lt y z) ∨ (lt z x ∧ lt x y) ∨ (lt y z ∧ lt z x)

theory ghost relation isNext (n : Nat) (next : Nat) :=
  n ∈ allNodes ∧ next ∈ allNodes ∧ n ≠ next ∧
  ∀ Z ∈ allNodes, Z ≠ n ∧ Z ≠ next → btw n next Z

assumption [allNodes_nodup] allNodes.Nodup
assumption [nextNode_isNext] ∀ N ∈ allNodes, isNext N (nextNode N)
assumption [nextNode_extends_between]
  ∀ S ∈ allNodes, ∀ D ∈ allNodes, ∀ N ∈ allNodes,
    btw S N (nextNode D) → N = D ∨ btw S N D
assumption [nextNode_closes_between]
  ∀ S ∈ allNodes, ∀ D ∈ allNodes, ∀ N ∈ allNodes,
    nextNode D = S → N = S ∨ N = D ∨ btw S N D
assumption [nextNode_no_between]
  ∀ S ∈ allNodes, ∀ N ∈ allNodes, btw S N (nextNode S) → N ≤ S

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
  let msg : Message := { payload := n, src := n, dst := th.nextNode n }
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
  let msg : Message := { payload := n, src := n, dst := th.nextNode n }
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
  let msg : Message := { payload := n, src := n, dst := th.nextNode n }
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
  rcases has with ⟨_, hnext, _⟩
  rcases hinv with ⟨_, _, _, _, _, _, hdst, _⟩
  have hnext_mem : th.nextNode n ∈ th.allNodes := (hnext n ht).2.1
  let msg : Message := { payload := n, src := n, dst := th.nextNode n }
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
  rcases has with ⟨_, hnext, _⟩
  rcases hinv with ⟨_, _, _, _, _, _, _, _, hself, _⟩
  have hnext_ne : n ≠ th.nextNode n := (hnext n ht).2.2.1
  let msg : Message := { payload := n, src := n, dst := th.nextNode n }
  by_cases hmem : msg ∈ st.messages
  · simpa [msg, hmem] using hself
  · simp [msg, hmem, List.mem_insertOrdered]
    exact ⟨fun heq _ _ => False.elim (hnext_ne heq), hself⟩

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
  rcases has with ⟨_, _, _, _, hno_between⟩
  rcases hinv with ⟨_, _, _, _, _, _, _, _, _, hdrop⟩
  let msg : Message := { payload := n, src := n, dst := th.nextNode n }
  by_cases hmem : msg ∈ st.messages
  · simpa [msg, hmem] using hdrop
  · simp [msg, hmem, List.mem_insertOrdered]
    exact ⟨hno_between n ht, hdrop⟩

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
  let msg : Message := { payload := m.payload, src := m.dst, dst := th.nextNode m.dst }
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
  let msg : Message := { payload := m.payload, src := m.dst, dst := th.nextNode m.dst }
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
  let msg : Message := { payload := m.payload, src := m.dst, dst := th.nextNode m.dst }
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
  rcases has with ⟨_, hnext, _⟩
  rcases hinv with ⟨_, _, _, _, _, _, hdst, _⟩
  have hdst_erase : ∀ msg' ∈ st.messages.erase m, msg'.dst ∈ th.allNodes := by
    intro msg' hm
    exact hdst msg' (List.mem_of_mem_erase hm)
  have hdst_m : m.dst ∈ th.allNodes := hdst m ht
  have hnext_dst : th.nextNode m.dst ∈ th.allNodes := (hnext m.dst hdst_m).2.1
  let msg : Message := { payload := m.payload, src := m.dst, dst := th.nextNode m.dst }
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
  rcases has with ⟨_, _, _, hcloses, _⟩
  rcases hinv with ⟨_, _, _, _, hpayload, _, hdst, _, hself, hdrop⟩
  have hself_erase :
      ∀ msg' ∈ st.messages.erase m, msg'.payload = msg'.dst → ∀ N ∈ th.allNodes, N ≤ msg'.payload := by
    intro msg' hm
    exact hself msg' (List.mem_of_mem_erase hm)
  have hpayload_m : m.payload ∈ th.allNodes := hpayload m ht
  have hdst_m : m.dst ∈ th.allNodes := hdst m ht
  let msg : Message := { payload := m.payload, src := m.dst, dst := th.nextNode m.dst }
  by_cases hcond : m.payload = m.dst ∧ m.dst ∉ st.leader
  · simpa [hcond] using hself_erase
  · by_cases hle : m.dst ≤ m.payload
    · by_cases hmem : msg ∈ st.messages.erase m
      · simpa [hcond, hle, msg, hmem] using hself_erase
      · have hnew_self :
            m.payload = th.nextNode m.dst → ∀ N ∈ th.allNodes, N ≤ m.payload := by
          intro hmsg_self N hN
          have hcases := hcloses m.payload hpayload_m m.dst hdst_m N hN hmsg_self.symm
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
  rcases has with ⟨_, _, hextends, _⟩
  rcases hinv with ⟨_, _, _, _, hpayload, _, hdst, _, _, hdrop⟩
  have hpayload_m : m.payload ∈ th.allNodes := hpayload m ht
  have hdst_m : m.dst ∈ th.allNodes := hdst m ht
  let msg : Message := { payload := m.payload, src := m.dst, dst := th.nextNode m.dst }
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
          have hcases := hextends m.payload hpayload_m m.dst hdst_m N hN hbtw
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
  { allNodes := [1, 5, 2, 4, 3],
    nextNode := fun n =>
        match n with
        | 1 => 5
        | 5 => 2
        | 2 => 4
        | 4 => 3
        | 3 => 1
        | _ => 0    -- we don't care about anything outside `allNodes`
   }

end RingOne
