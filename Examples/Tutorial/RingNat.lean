import Veil
import Init.Data.List.Erase


veil module RingFin


abbrev node := Fin 8

individual leader : List node

@[veil_decl] structure Message (node : Type) where
  payload : node
  src : node
  dst : node

individual messages : List (Message node)

#gen_state

abbrev nextNode (n : node) : node := n + 1
-- assumption [le_refl] ∀ n, le n n

after_init {
  leader := []
  messages := []
}

procedure sendToNext (payload src : node) {
  let msg := Message.mk payload src (nextNode src)
  if msg ∉ messages then
    messages := msg :: messages
}

action send (n : node) {
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
invariant [leader_greatest] L ∈ leader → N ≤ L
invariant [drop_smaller] M ∈ messages → M.src ≤ M.payload
invariant [self_msg_greatest] M ∈ messages ∧ M.dst = M.payload → N ≤ M.dst
invariant [messages_nodup] messages.Nodup

#gen_spec

#check_invariants


theorem recv_doesNotThrow (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ]
    [recv_dec_0 :
      (__do_lift : State χ) →
        (x : Message node) → Decidable (@List.Mem.{0} (Message node) x ((χ_rep State.Label.messages).1 __do_lift.2))] :
    ∀ (__veil_ex : Int),
      Veil.VeilM.doesNotThrowAssuming_ex (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub recv_dec_0)
        (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) __veil_ex :=
  by
  veil_human


theorem initializer_single_leader (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@initializer.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@single_leader ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  grind

theorem initializer_leader_greatest (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@initializer.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@leader_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  grind

theorem initializer_drop_smaller (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@initializer.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@drop_smaller ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  grind

theorem initializer_self_msg_greatest (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@initializer.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@self_msg_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  grind

theorem initializer_messages_nodup (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@initializer.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@messages_nodup ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  grind

theorem send_single_leader (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    ∀ (n : node),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub n)
        (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@single_leader ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  grind

theorem send_leader_greatest (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    ∀ (n : node),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub n)
        (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@leader_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  grind

theorem send_drop_smaller (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    ∀ (n : node),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub n)
        (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@drop_smaller ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  grind

theorem send_self_msg_greatest (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    ∀ (n : node),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub n)
        (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@self_msg_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  grind

theorem send_messages_nodup (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    ∀ (n : node),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@send.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub n)
        (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@messages_nodup ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  grind

theorem recv_single_leader (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ]
    [recv_dec_0 :
      (__do_lift : State χ) →
        (x : Message node) → Decidable (@List.Mem.{0} (Message node) x ((χ_rep State.Label.messages).1 __do_lift.2))] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub recv_dec_0)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@single_leader ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  split_ifs <;> try grind
  {
    simp only [List.length_cons, Nat.reduceLeDiff, Nat.le_zero_eq, List.length_eq_zero_iff]


  }

theorem recv_leader_greatest (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ]
    [recv_dec_0 :
      (__do_lift : State χ) →
        (x : Message node) → Decidable (@List.Mem.{0} (Message node) x ((χ_rep State.Label.messages).1 __do_lift.2))] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub recv_dec_0)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@leader_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  grind

theorem recv_drop_smaller (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ]
    [recv_dec_0 :
      (__do_lift : State χ) →
        (x : Message node) → Decidable (@List.Mem.{0} (Message node) x ((χ_rep State.Label.messages).1 __do_lift.2))] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub recv_dec_0)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@drop_smaller ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  grind

theorem recv_self_msg_greatest (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ]
    [recv_dec_0 :
      (__do_lift : State χ) →
        (x : Message node) → Decidable (@List.Mem.{0} (Message node) x ((χ_rep State.Label.messages).1 __do_lift.2))] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub recv_dec_0)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@self_msg_greatest ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  split_ifs <;> try grind


theorem recv_messages_nodup (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ]
    [recv_dec_0 :
      (__do_lift : State χ) →
        (x : Message node) → Decidable (@List.Mem.{0} (Message node) x ((χ_rep State.Label.messages).1 __do_lift.2))] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@recv.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub recv_dec_0)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@messages_nodup ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  grind

-- #model_check { node := Fin 4 }
-- { nextNode := fun n => n + 1,
--   le := fun n m => n < m }

end RingFin
