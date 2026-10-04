module

public import Veil

set_option veil.smt.trust false

-- Ghost functions must unfold before SMT translation on both WP paths
-- and on the local TR path.
veil module GhostFunctionVC

type node
relation a : node → Bool
relation b : node → Bool

ghost function aVal (n : node) : Bool := a n

after_init {
  a N := false
  b N := false
}

action setFn (n : node) {
  require aVal n = true
  b n := true
}

invariant [b_implies_a] b N → a N

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  b_implies_a ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  setFn
    doesNotThrow ... ✅
    b_implies_a ... ✅
-/
#guard_msgs in
#check_invariants

-- Exercise each path explicitly so that fallback cannot mask a regression.
variable (ρ σ node : Type) [DecidableEq node] [Inhabited node]
  (χ : State.Label → Type)
  [χ_rep : ∀ f, Veil.FieldRepresentation
    (State.Label.toDomain node f) (State.Label.toCodomain node f) (χ f)]
  [∀ f, Veil.LawfulFieldRepresentation
    (State.Label.toDomain node f) (State.Label.toCodomain node f) (χ f) (χ_rep f)]
  [IsSubStateOf (State χ) σ] [IsSubReaderOf (Theory node) ρ]

example (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (setFn.ext (ρ := ρ) (σ := σ) (χ := χ) n)
      (Assumptions ρ node) (Invariants ρ σ node χ) (@b_implies_a ρ σ node _ _ χ _ _ _ _) := by
  veil_apply_local_wp
  __veil_solve_wplo

example (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (setFn.ext (ρ := ρ) (σ := σ) (χ := χ) n)
      (Assumptions ρ node) (Invariants ρ σ node χ) (@b_implies_a ρ σ node _ _ χ _ _ _ _) := by
  veil_intros
  __veil_solve_wp_conservative

example (n : node) :
    Veil.Transition.meetsSpecificationIfSuccessfulAssuming
      (@setFn.ext.tr ρ σ node _ _ χ _ _ _ _ n)
      (Assumptions ρ node) (Invariants ρ σ node χ) (@b_implies_a ρ σ node _ _ χ _ _ _ _) := by
  veil_apply_local_tr
  __veil_solve_trlo

end GhostFunctionVC

veil module TheoryGhostFunctionVC

type node
immutable relation a : node → Bool
relation b : node → Bool

theory ghost function aVal (n : node) : Bool := a n

after_init { b N := false }

action setFn (n : node) {
  require aVal n = true
  b n := true
}

invariant [b_implies_a] b N → a N

#gen_spec

variable (ρ σ node : Type) [DecidableEq node] [Inhabited node]
  (χ : State.Label → Type)
  [χ_rep : ∀ f, Veil.FieldRepresentation
    (State.Label.toDomain node f) (State.Label.toCodomain node f) (χ f)]
  [∀ f, Veil.LawfulFieldRepresentation
    (State.Label.toDomain node f) (State.Label.toCodomain node f) (χ f) (χ_rep f)]
  [IsSubStateOf (State χ) σ] [IsSubReaderOf (Theory node) ρ]

example (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (setFn.ext (ρ := ρ) (σ := σ) (χ := χ) n)
      (Assumptions ρ node) (Invariants ρ σ node χ) (@b_implies_a ρ σ node _ _ χ _ _ _ _) := by
  veil_intros
  __veil_solve_wp_conservative

end TheoryGhostFunctionVC
