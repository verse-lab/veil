import Veil
-- https://github.com/aman-goel/ivybench/blob/d2c9298fdd099001c71a34bc2e118db6f07d8404/multisig/ivy/multisig-majority.ivy


veil module MultiSigMajority

type validator
type destination
type value
type deadline
type signature
type quorum

relation holding : validator → Bool
relation collect : validator → destination → value → deadline → Bool

relation sig : validator → destination → value → deadline → signature → Bool
relation sig_auth : signature → Bool

relation proposed : validator → destination → value → deadline → Bool
relation paid : validator → destination → value → deadline → Bool
relation cancelled : validator → destination → value → deadline → Bool

relation expired : deadline → Bool

immutable relation member : signature → quorum → Bool

#gen_state
ghost relation chosenAt (Q:quorum) (N:validator) (K:destination) (V:value) (D:deadline) := ∀ S, member S Q -> sig N K V D S
ghost relation chosen (N:validator) (K:destination) (V:value) (D:deadline) := ∃ q, chosenAt q N K V D

assumption ∀ (q1 q2 : quorum), ∃ (s : signature), member s q1 ∧ member s q2

after_init {
  holding N := true;
  collect N K V D := false;

  proposed N K V D := false;
  paid N K V D := false;
  cancelled N K V D := false;

  sig N K V D S := false
}


action pay (n: validator) (k: destination) (v: value) (d: deadline) {
  require collect n k v d;
  require ¬ expired d;
  require chosen n k v d;

  paid n k v d := true;
  holding n := true;
  collect n k v d := false
}

safety [cancelled_after_deadline] cancelled N K V D → expired D
safety [paid_if_enough_sigs] paid N K V D → (∃ q, ∀ s, (member s q) → (sig N K V D s ∧ sig_auth s))
safety [paid_imp_proposed] paid N K V D → proposed N K V D

invariant [ic3po_global2] collect V1 D1 V2 D2 → proposed V1 D1 V2 D2
invariant [ic3po_global3] sig V1 D1 V2 D2 S1 → sig_auth S1

#gen_spec

#guard_msgs(drop warning) in
theorem pay_paid_imp_proposed_tr (ρ : Type) (σ : Type) (validator : Type) [validator_dec_eq : DecidableEq.{1} validator]
    [validator_inhabited : Inhabited.{1} validator] (destination : Type)
    [destination_dec_eq : DecidableEq.{1} destination] [destination_inhabited : Inhabited.{1} destination]
    (value : Type) [value_dec_eq : DecidableEq.{1} value] [value_inhabited : Inhabited.{1} value] (deadline : Type)
    [deadline_dec_eq : DecidableEq.{1} deadline] [deadline_inhabited : Inhabited.{1} deadline] (signature : Type)
    [signature_dec_eq : DecidableEq.{1} signature] [signature_inhabited : Inhabited.{1} signature] (quorum : Type)
    [quorum_dec_eq : DecidableEq.{1} quorum] [quorum_inhabited : Inhabited.{1} quorum] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain validator destination value deadline signature quorum __veil_f)
          (State.Label.toCodomain validator destination value deadline signature quorum __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation
          (State.Label.toDomain validator destination value deadline signature quorum __veil_f)
          (State.Label.toCodomain validator destination value deadline signature quorum __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub : IsSubReaderOf (@Theory validator destination value deadline signature quorum) ρ]
    [pay_dec_0 :
      (n : validator) →
        (k : destination) →
          (v : value) →
            (d : deadline) →
              (__do_lift : State χ) →
                (__do_lift_1 : Theory validator destination value deadline signature quorum) →
                  Decidable
                    (∃ (q : quorum),
                      ∀ (S : signature),
                        @Eq.{1} Bool
                            (@Theory.member validator destination value deadline signature quorum __do_lift_1 S q)
                            true →
                          @Eq.{1} Bool
                            (@Veil.FieldRepresentation.get
                              (State.Label.toDomain validator destination value deadline signature quorum
                                State.Label.sig)
                              (State.Label.toCodomain validator destination value deadline signature quorum
                                State.Label.sig)
                              (χ State.Label.sig) (χ_rep State.Label.sig) __do_lift.3 n k v d S)
                            true)] :
    ∀ (n : validator) (k : destination) (v : value) (d : deadline),
      Veil.Transition.meetsSpecificationIfSuccessfulAssuming
        (@pay.ext.tr ρ σ validator validator_dec_eq validator_inhabited destination destination_dec_eq
          destination_inhabited value value_dec_eq value_inhabited deadline deadline_dec_eq deadline_inhabited signature
          signature_dec_eq signature_inhabited quorum quorum_dec_eq quorum_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub
          pay_dec_0 n k v d)
        (@Assumptions ρ validator validator_dec_eq validator_inhabited destination destination_dec_eq
          destination_inhabited value value_dec_eq value_inhabited deadline deadline_dec_eq deadline_inhabited signature
          signature_dec_eq signature_inhabited quorum quorum_dec_eq quorum_inhabited ρ_sub)
        (@Invariants ρ σ validator validator_dec_eq validator_inhabited destination destination_dec_eq
          destination_inhabited value value_dec_eq value_inhabited deadline deadline_dec_eq deadline_inhabited signature
          signature_dec_eq signature_inhabited quorum quorum_dec_eq quorum_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@paid_imp_proposed ρ σ validator validator_dec_eq validator_inhabited destination destination_dec_eq
          destination_inhabited value value_dec_eq value_inhabited deadline deadline_dec_eq deadline_inhabited signature
          signature_dec_eq signature_inhabited quorum quorum_dec_eq quorum_inhabited χ χ_rep χ_rep_lawful σ_sub
          ρ_sub) :=
  by
  veil_solve_tr

end MultiSigMajority
