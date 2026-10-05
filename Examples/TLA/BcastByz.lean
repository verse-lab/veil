module

public import Veil

open Std
/-
src : https://github.com/tlaplus/Examples/blob/master/specifications/bcastByz/bcastByz.tla
This file specifies the Byzantine broadcast protocol in Veil, which is a
TLA+ encoding of a parameterized model of the broadcast distributed algorithm
with Byzantine faults.

This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:

[1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
simple fault-tolerant algorithms. Distributed Computing 1987,
Volume 2, Issue 2, pp 80-94

The protocol works as follows:
- There are N processes, of which F can be faulty (Byzantine)
- There are T >= F possible faulty processes
- The constraint is N > 3*T
- Processes can be in states: V0 (no INIT), V1 (received INIT), SE (sent ECHO), AC (accepted)
- Correct processes send ECHO messages based on certain conditions
- A correct process accepts when it receives enough ECHO messages

-/
veil module BcastByz

type process
type procSet
instantiate pset : TSet process procSet
-- instantiate thread : Fintype process

enum PCState = { V0, V1, SE, AC }

-- N: total number of processes
-- T: upper bound on Byzantine processes
-- F: actual number of faulty processes
immutable individual N : Nat
immutable individual T : Nat
immutable individual F : Nat
-- immutable individual Proc : procSet

instantiate processEnumerable : Veil.Enumeration process

-- State variables

-- M == { "ECHO" }
-- immutable individual M : process
-- (* ByzMsgs == { <<p, "ECHO">> : p \in Faulty }: quite complicated to write a TLAPS proof
--    for the cardinality of the expression { e : x \in S}
--  *)

-- individual Corr : Finset process    -- correct processes
individual Corr : procSet
individual Faulty : procSet             -- faulty processes
function pc (p : process) : PCState  -- control state of each process
-- relation pointer (ph : phase)             -- current phase of the protocol

-- In TLA+: sent \subseteq Proc \times M
-- Since all messages are <<p, "ECHO">>, we only need to track which processes have sent
-- sent is the set of processes that have sent messages
-- relation sent (p : process)
individual sent : procSet
function rcvd (receiver : process) : procSet

veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

-- Ghost definitions for readability
ghost relation isCorrect (p : process) := pset.contains p Corr
ghost relation isFaulty (p : process) := pset.contains p Faulty

-- Parameter constraints, from `ASSUME NTF` in bcastByz.tla.
assumption [n_gt_3t] N > 3 * T
assumption [t_ge_f] T ≥ F
-- `Proc == 1 .. N` in TLA+: the set of all processes has cardinality `N`.
assumption [card_proc] pset.count (pset.ofList processEnumerable.allValues) = N

-- Initial state

-- Init ==
--   /\ sent = {}                          (* No messages sent initially *)
--   /\ pc \in [ Proc -> {"V0", "V1"} ]    (* Some processes received INIT messages, some didn't *)
--   /\ rcvd = [ i \in Proc |-> {} ]       (* No messages received initially *)
--   /\ Corr \in SUBSET Proc
--   /\ Cardinality(Corr) = N - F          (* N - F processes are correct, but their identities are unknown*)
--   /\ Faulty = Proc \ Corr               (* The rest (F) are faulty*)
after_init {
  sent := pset.empty
  rcvd P := pset.empty
  let V1Set ← pick procSet
  pc P := if pset.contains P V1Set then V1 else V0
  let corrSet :| pset.count corrSet = N - F
  Corr := corrSet
  Faulty := pset.diff (pset.ofList processEnumerable.allValues) Corr
}

-- ByzMsgs == Faulty \X M

-- Receive(self, includeByz) ==
--   \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
--     rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMessages ]
-- ReceiveFromCorrectSender(self) == Receive(self, FALSE)
-- ReceiveFromAnySender(self) == Receive(self, TRUE)
procedure Receive (self : process) (includeByz : Bool) {
  let superSet := if includeByz then pset.union sent Faulty else sent
  let newMessages :| pset.isSubset newMessages superSet
  rcvd self := pset.union (rcvd self) newMessages
}

-- NOTE: `ReceiveFromCorrectSender` is not used in the `Step` part

procedure ReceiveFromAnySender (self : process) {
  Receive self true
}

/- This action is used to model the behavior of a process
doing nothing (stuttering) in TLA+, which corresponding to Line 160:
  `\/ UNCHANGED vars (* add a self-loop for terminating computations *)`
in bcastByz.tla.
With this action, we can not only obtain the same
number of `distinct states` as TLA+ verision, but `total states` as well.-/
action Stutter {
  pure ()
}

-- UponV1(self) ==
--   /\ pc[self] = "V1"
--   /\ pc' = [pc EXCEPT ![self] = "SE"]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action Step_UponV1 (self : process) {
  require isCorrect self
  require pc self = V1
  ReceiveFromAnySender self
  pc self := SE
  sent := pset.insert self sent
}

-- UponNonFaulty(self) ==
--   /\ pc[self] \in { "V0", "V1" }
--   /\ Cardinality(rcvd'[self]) >= N - 2*T
--   /\ Cardinality(rcvd'[self]) < N - T
--   /\ pc' = [ pc EXCEPT ![self] = "SE" ]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action Step_UponNonFaulty (self : process) {
  require isCorrect self
  require pc self ∈ [V0, V1]
  ReceiveFromAnySender self
  assume pset.count (rcvd self) ≥ N - 2 * T
  assume pset.count (rcvd self) < N - T
  pc self := SE
  sent := pset.insert self sent
}

-- UponAcceptNotSentBefore(self) ==
--   /\ pc[self] \in { "V0", "V1" }
--   /\ Cardinality(rcvd'[self]) >= N - T
--   /\ pc' = [ pc EXCEPT ![self] = "AC" ]
--   /\ sent' = sent \cup { <<self, "ECHO">> }
--   /\ UNCHANGED << Corr, Faulty >>
action Step_UponAcceptNotSentBefore (self : process) {
  require isCorrect self
  require pc self ∈ [V0, V1]
  ReceiveFromAnySender self
  assume pset.count (rcvd self) ≥ N - T
  pc self := AC
  sent := pset.insert self sent
}

-- UponAcceptSentBefore(self) ==
--   /\ pc[self] = "SE"
--   /\ Cardinality(rcvd'[self]) >= N - T
--   /\ pc' = [pc EXCEPT ![self] = "AC"]
--   /\ sent' = sent
--   /\ UNCHANGED << Corr, Faulty >>
action Step_UponAcceptorSentBefore (self : process) {
  require isCorrect self
  require pc self = SE
  ReceiveFromAnySender self
  assume pset.count (rcvd self) ≥ N - T
  pc self := AC
}

-- Step(self) ==
--   /\ ReceiveFromAnySender(self)
--   /\ \/ UponV1(self)
--      \/ UponNonFaulty(self)
--      \/ UponAcceptNotSentBefore(self)
--      \/ UponAcceptSentBefore(self)

-- Parameter constraints from TLA+ specification
-- TypeOK == /\ N \in Nat \ {0}
--           /\ T \in Nat
--           /\ F \in Nat
--           /\ N > 3 * T
--           /\ T >= F
-- procedure ByzMsgs {
--   return pset.remove M Faulty
-- }

-- FCConstraints from bcastByz.tla:
--   /\ Corr \cup Faulty = Proc
--   /\ Cardinality(Corr) >= N - T
--   /\ Cardinality(Faulty) <= T
invariant [Corr_cup_faulty_eq_proc] pset.union Corr Faulty == (pset.ofList processEnumerable.allValues)
invariant [card_corr] pset.count Corr ≥ N - T
invariant [card_faulty] pset.count Faulty ≤ T

#gen_spec

#model_check
{ process := (Fin 4),
  procSet := OrdList (Fin 4) }
{ N := 4,
  T := 1,
  F := 1 }

-- This takes more time
-- #model_check compiled
-- { process := (Fin 5),
--   procSet := OrdList (Fin 5) }
-- { N := 5,
--   T := 1,
--   F := 1 }


/- Interactive proofs of the verification conditions of `#check_invariants`
above (the SMT backend cannot reason about `TSet` cardinalities). The theorem
`<action>_<invariant>` states that `<action>` preserves `<invariant>`, and
`initializer_<invariant>` that the initializer establishes it. The statements
are the stubs generated by `#check_invariants`; only the proofs are hand-written. -/

-- Initialization establishes `Corr ∪ Faulty = Proc`. Since `Faulty` is defined as
-- `Proc \ Corr`, the two sides have the same elements (every process is in
-- `Proc` by `Enumeration.complete`), hence are equal by set extensionality (`TSet.ext`).
@[veil]
theorem initializer_Corr_cup_faulty_eq_proc (ρ : Type) (σ : Type) (process : Type)
    [process_dec_eq : DecidableEq.{1} process] [process_inhabited : Inhabited.{1} process] (procSet : Type)
    [procSet_dec_eq : DecidableEq.{1} procSet] [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet]
    (PCState : Type) [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@initializer.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset
        PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
      (fun _ _ => True)
      (@Corr_cup_faulty_eq_proc ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited
        pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub
        ρ_sub) :=
  by
  unveil
  intro _
  apply TSet.ext
  intro e
  have he := (TSet.contains_ofList (κ := procSet) e processEnumerable.allValues).mpr (Veil.Enumeration.complete e)
  rw [TSet.contains_union, TSet.contains_diff, he]
  cases TSet.contains e corrSet <;> rfl

-- Initialization establishes `|Corr| ≥ N - T`: `|Corr| = N - F` and `F ≤ T`.
@[veil]
theorem initializer_card_corr (ρ : Type) (σ : Type) (process : Type) [process_dec_eq : DecidableEq.{1} process]
    [process_inhabited : Inhabited.{1} process] (procSet : Type) [procSet_dec_eq : DecidableEq.{1} procSet]
    [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet] (PCState : Type)
    [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@initializer.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset
        PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
      (fun _ _ => True)
      (@card_corr ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intro hcount
  obtain ⟨_, htf, _⟩ := has
  omega

-- Initialization establishes `|Faulty| ≤ T`: since `Corr ⊆ Proc` and
-- `Faulty = Proc \ Corr`, `|Faulty| + |Corr| = |Proc| = N`
-- (`TSet.count_diff_add_count_of_subset`); with `|Corr| = N - F` and `F ≤ T` this gives the bound.
@[veil]
theorem initializer_card_faulty (ρ : Type) (σ : Type) (process : Type) [process_dec_eq : DecidableEq.{1} process]
    [process_inhabited : Inhabited.{1} process] (procSet : Type) [procSet_dec_eq : DecidableEq.{1} procSet]
    [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet] (PCState : Type)
    [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@initializer.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset
        PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
      (fun _ _ => True)
      (@card_faulty ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  classical
  intro hcorr
  obtain ⟨_, htf, hcard⟩ := has
  have hsub : TSet.isSubset corrSet (TSet.ofList processEnumerable.allValues) := by
    intro p _
    exact (TSet.contains_ofList p processEnumerable.allValues).mpr (Veil.Enumeration.complete p)
  have hdiff := TSet.count_diff_add_count_of_subset (TSet.ofList processEnumerable.allValues) corrSet hsub
  omega

-- `Stutter` leaves the state unchanged, so `Corr ∪ Faulty = Proc` carries over from the pre-state.
@[veil]
theorem Stutter_Corr_cup_faulty_eq_proc (ρ : Type) (σ : Type) (process : Type)
    [process_dec_eq : DecidableEq.{1} process] [process_inhabited : Inhabited.{1} process] (procSet : Type)
    [procSet_dec_eq : DecidableEq.{1} procSet] [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet]
    (PCState : Type) [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@Stutter.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
      (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Corr_cup_faulty_eq_proc ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited
        pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub
        ρ_sub) :=
  by
  unveil
  intros
  exact hinv.1

-- `Stutter` leaves the state unchanged, so `|Corr| ≥ N - T` carries over from the pre-state.
@[veil]
theorem Stutter_card_corr (ρ : Type) (σ : Type) (process : Type) [process_dec_eq : DecidableEq.{1} process]
    [process_inhabited : Inhabited.{1} process] (procSet : Type) [procSet_dec_eq : DecidableEq.{1} procSet]
    [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet] (PCState : Type)
    [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@Stutter.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
      (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@card_corr ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intros
  exact hinv.2.1

-- `Stutter` leaves the state unchanged, so `|Faulty| ≤ T` carries over from the pre-state.
@[veil]
theorem Stutter_card_faulty (ρ : Type) (σ : Type) (process : Type) [process_dec_eq : DecidableEq.{1} process]
    [process_inhabited : Inhabited.{1} process] (procSet : Type) [procSet_dec_eq : DecidableEq.{1} procSet]
    [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet] (PCState : Type)
    [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@Stutter.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
      (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@card_faulty ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
        PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intros
  exact hinv.2.2

-- `Step_UponV1` does not modify `Corr` or `Faulty`, so `Corr ∪ Faulty = Proc` carries over from the pre-state.
@[veil]
theorem Step_UponV1_Corr_cup_faulty_eq_proc (ρ : Type) (σ : Type) (process : Type)
    [process_dec_eq : DecidableEq.{1} process] [process_inhabited : Inhabited.{1} process] (procSet : Type)
    [procSet_dec_eq : DecidableEq.{1} procSet] [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet]
    (PCState : Type) [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Step_UponV1.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset
          PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub self)
        (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@Corr_cup_faulty_eq_proc ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited
          pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub
          ρ_sub) :=
  by
  unveil
  intros
  exact hinv.1

-- `Step_UponV1` does not modify `Corr` or `Faulty`, so `|Corr| ≥ N - T` carries over from the pre-state.
@[veil]
theorem Step_UponV1_card_corr (ρ : Type) (σ : Type) (process : Type) [process_dec_eq : DecidableEq.{1} process]
    [process_inhabited : Inhabited.{1} process] (procSet : Type) [procSet_dec_eq : DecidableEq.{1} procSet]
    [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet] (PCState : Type)
    [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Step_UponV1.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset
          PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub self)
        (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@card_corr ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intros
  exact hinv.2.1

-- `Step_UponV1` does not modify `Corr` or `Faulty`, so `|Faulty| ≤ T` carries over from the pre-state.
@[veil]
theorem Step_UponV1_card_faulty (ρ : Type) (σ : Type) (process : Type) [process_dec_eq : DecidableEq.{1} process]
    [process_inhabited : Inhabited.{1} process] (procSet : Type) [procSet_dec_eq : DecidableEq.{1} procSet]
    [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet] (PCState : Type)
    [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Step_UponV1.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset
          PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub self)
        (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@card_faulty ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intros
  exact hinv.2.2

-- `Step_UponNonFaulty` does not modify `Corr` or `Faulty`, so `Corr ∪ Faulty = Proc` carries over from the pre-state.
@[veil]
theorem Step_UponNonFaulty_Corr_cup_faulty_eq_proc (ρ : Type) (σ : Type) (process : Type)
    [process_dec_eq : DecidableEq.{1} process] [process_inhabited : Inhabited.{1} process] (procSet : Type)
    [procSet_dec_eq : DecidableEq.{1} procSet] [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet]
    (PCState : Type) [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Step_UponNonFaulty.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited
          pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub
          self)
        (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@Corr_cup_faulty_eq_proc ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited
          pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub
          ρ_sub) :=
  by
  unveil
  intros
  exact hinv.1

-- `Step_UponNonFaulty` does not modify `Corr` or `Faulty`, so `|Corr| ≥ N - T` carries over from the pre-state.
@[veil]
theorem Step_UponNonFaulty_card_corr (ρ : Type) (σ : Type) (process : Type) [process_dec_eq : DecidableEq.{1} process]
    [process_inhabited : Inhabited.{1} process] (procSet : Type) [procSet_dec_eq : DecidableEq.{1} procSet]
    [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet] (PCState : Type)
    [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Step_UponNonFaulty.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited
          pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub
          self)
        (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@card_corr ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intros
  exact hinv.2.1

-- `Step_UponNonFaulty` does not modify `Corr` or `Faulty`, so `|Faulty| ≤ T` carries over from the pre-state.
@[veil]
theorem Step_UponNonFaulty_card_faulty (ρ : Type) (σ : Type) (process : Type) [process_dec_eq : DecidableEq.{1} process]
    [process_inhabited : Inhabited.{1} process] (procSet : Type) [procSet_dec_eq : DecidableEq.{1} procSet]
    [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet] (PCState : Type)
    [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Step_UponNonFaulty.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited
          pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub
          self)
        (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@card_faulty ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intros
  exact hinv.2.2

-- `Step_UponAcceptNotSentBefore` does not modify `Corr` or `Faulty`, so `Corr ∪ Faulty = Proc` carries over from the pre-state.
@[veil]
theorem Step_UponAcceptNotSentBefore_Corr_cup_faulty_eq_proc (ρ : Type) (σ : Type) (process : Type)
    [process_dec_eq : DecidableEq.{1} process] [process_inhabited : Inhabited.{1} process] (procSet : Type)
    [procSet_dec_eq : DecidableEq.{1} procSet] [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet]
    (PCState : Type) [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Step_UponAcceptNotSentBefore.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq
          procSet_inhabited pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep
          χ_rep_lawful σ_sub ρ_sub self)
        (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@Corr_cup_faulty_eq_proc ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited
          pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub
          ρ_sub) :=
  by
  unveil
  intros
  exact hinv.1

-- `Step_UponAcceptNotSentBefore` does not modify `Corr` or `Faulty`, so `|Corr| ≥ N - T` carries over from the pre-state.
@[veil]
theorem Step_UponAcceptNotSentBefore_card_corr (ρ : Type) (σ : Type) (process : Type)
    [process_dec_eq : DecidableEq.{1} process] [process_inhabited : Inhabited.{1} process] (procSet : Type)
    [procSet_dec_eq : DecidableEq.{1} procSet] [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet]
    (PCState : Type) [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Step_UponAcceptNotSentBefore.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq
          procSet_inhabited pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep
          χ_rep_lawful σ_sub ρ_sub self)
        (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@card_corr ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intros
  exact hinv.2.1

-- `Step_UponAcceptNotSentBefore` does not modify `Corr` or `Faulty`, so `|Faulty| ≤ T` carries over from the pre-state.
@[veil]
theorem Step_UponAcceptNotSentBefore_card_faulty (ρ : Type) (σ : Type) (process : Type)
    [process_dec_eq : DecidableEq.{1} process] [process_inhabited : Inhabited.{1} process] (procSet : Type)
    [procSet_dec_eq : DecidableEq.{1} procSet] [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet]
    (PCState : Type) [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Step_UponAcceptNotSentBefore.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq
          procSet_inhabited pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep
          χ_rep_lawful σ_sub ρ_sub self)
        (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@card_faulty ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intros
  exact hinv.2.2

-- `Step_UponAcceptorSentBefore` does not modify `Corr` or `Faulty`, so `Corr ∪ Faulty = Proc` carries over from the pre-state.
@[veil]
theorem Step_UponAcceptorSentBefore_Corr_cup_faulty_eq_proc (ρ : Type) (σ : Type) (process : Type)
    [process_dec_eq : DecidableEq.{1} process] [process_inhabited : Inhabited.{1} process] (procSet : Type)
    [procSet_dec_eq : DecidableEq.{1} procSet] [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet]
    (PCState : Type) [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Step_UponAcceptorSentBefore.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq
          procSet_inhabited pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep
          χ_rep_lawful σ_sub ρ_sub self)
        (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@Corr_cup_faulty_eq_proc ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited
          pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub
          ρ_sub) :=
  by
  unveil
  intros
  exact hinv.1

-- `Step_UponAcceptorSentBefore` does not modify `Corr` or `Faulty`, so `|Corr| ≥ N - T` carries over from the pre-state.
@[veil]
theorem Step_UponAcceptorSentBefore_card_corr (ρ : Type) (σ : Type) (process : Type)
    [process_dec_eq : DecidableEq.{1} process] [process_inhabited : Inhabited.{1} process] (procSet : Type)
    [procSet_dec_eq : DecidableEq.{1} procSet] [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet]
    (PCState : Type) [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Step_UponAcceptorSentBefore.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq
          procSet_inhabited pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep
          χ_rep_lawful σ_sub ρ_sub self)
        (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@card_corr ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intros
  exact hinv.2.1

-- `Step_UponAcceptorSentBefore` does not modify `Corr` or `Faulty`, so `|Faulty| ≤ T` carries over from the pre-state.
@[veil]
theorem Step_UponAcceptorSentBefore_card_faulty (ρ : Type) (σ : Type) (process : Type)
    [process_dec_eq : DecidableEq.{1} process] [process_inhabited : Inhabited.{1} process] (procSet : Type)
    [procSet_dec_eq : DecidableEq.{1} procSet] [procSet_inhabited : Inhabited.{1} procSet] [pset : TSet process procSet]
    (PCState : Type) [PCState_dec_eq : DecidableEq.{1} PCState] [PCState_inhabited : Inhabited.{1} PCState]
    [PCState_Enum : @PCState_EnumClass PCState] [processEnumerable : Veil.Enumeration process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process procSet PCState __veil_f)
          (State.Label.toCodomain process procSet PCState __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process procSet PCState) ρ] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Step_UponAcceptorSentBefore.ext ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq
          procSet_inhabited pset PCState PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep
          χ_rep_lawful σ_sub ρ_sub self)
        (@Assumptions ρ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@card_faulty ρ σ process process_dec_eq process_inhabited procSet procSet_dec_eq procSet_inhabited pset PCState
          PCState_dec_eq PCState_inhabited PCState_Enum processEnumerable χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  intros
  exact hinv.2.2

#check_invariants


end BcastByz
