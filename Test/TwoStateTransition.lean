import Veil
import Test.TestUtil

veil module TwoStateTransitionTest

type address

relation initial_msg (originator : address) (dst : address) (r : address) (v : address)
relation is_byz : address → Bool

#gen_state

after_init {
  initial_msg O D R V := false
}

#guard_msgs in
transition byz {
  (∀ (src dst : address) (r : address) (v : address),
    (¬ is_byz src ∧ (initial_msg src dst r v ↔ initial_msg' src dst r v)) ∨
    (is_byz src ∧ (initial_msg src dst r v → initial_msg' src dst r v)))
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``byz


#guard_msgs in
transition withargs (r : address) {
  (∀ (src dst : address) (v : address),
    (¬ is_byz src ∧ (initial_msg src dst r v ↔ initial_msg' src dst r v)) ∨
    (is_byz src ∧ (initial_msg src dst r v → initial_msg' src dst r v)))
}

/-- info: true -/
#guard_msgs in
#eval isElaboratedCorrectly ``withargs

invariant true

-- FIXME: this is a bug
/-- warning: you have not defined any actions for this specification; did you forget? -/
#guard_msgs in
#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  inv_0 ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  byz
    doesNotThrow ... ✅
    inv_0 ... ✅
  withargs
    doesNotThrow ... ✅
    inv_0 ... ✅
-/
#guard_msgs in
#check_invariants

-- This checks that the TR version also works
#guard_msgs in
theorem byz_inv_0_tr (ρ : Type) (σ : Type) (address : Type) [address_dec_eq : DecidableEq.{1} address]
    [address_inhabited : Inhabited.{1} address] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain address __veil_f) (State.Label.toCodomain address __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain address __veil_f) (State.Label.toCodomain address __veil_f)
          (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory address) ρ] :
    Veil.Transition.meetsSpecificationIfSuccessfulAssuming
      (@byz.ext.tr ρ σ address address_dec_eq address_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ address address_dec_eq address_inhabited ρ_sub)
      (@Invariants ρ σ address address_dec_eq address_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@inv_0 ρ σ address address_dec_eq address_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by veil_solve_tr

end TwoStateTransitionTest
