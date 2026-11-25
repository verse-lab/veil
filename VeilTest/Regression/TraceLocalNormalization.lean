module
public import Veil
public section

/-! Semantic regressions for per-transition normalization. The manual theorems
below are kernel checked; SAT commands also exercise trace model decoding. -/

section LogicalScopes
open Lean Elab Tactic

-- An inactive branch with an empty witness domain must stay satisfiable.
theorem inactive_empty_witness :
    ¬¬ (True ∨ (∃ _f : Unit → Empty, True)) := by
  __veil_bmc_normalize
  exact fun h => h trivial

-- Quantifier dependence cannot be exchanged even when both types are inhabited.
theorem dependent_choice_scope :
    (∀ x : Bool, ∃ f : Unit → Bool, f () = x) ∧
    ¬ (∃ f : Unit → Bool, ∀ x : Bool, f () = x) := by
  constructor
  · intro x; exact ⟨fun _ => x, rfl⟩
  · __veil_bmc_normalize
    intro f h
    exact Bool.noConfusion ((h true).symm.trans (h false))

-- Distinct witnesses retain their scopes, and dependent witness types stay scoped.
theorem independent_and_dependent_witnesses :
    ¬ (((∃ f : Unit → Bool, f () = true) ∧ (∃ g : Unit → Bool, g () = false)) ∧
        (∀ f : Unit → Bool, f () = true)) := by
  __veil_bmc_normalize
  intro f g h
  exact Bool.noConfusion ((h.2 g).symm.trans h.1.2)

theorem dependent_witness_type :
    ¬ ((∃ n : Nat, ∃ w : Fin (n + 1), w.val > n) ∧ True) := by
  __veil_bmc_normalize
  intro n w h
  have := h.1
  have := w.isLt
  omega

-- Background hypotheses remain hints. Initialization, steps, and assertions
-- stay in one target, with the original order and parenthesization.
example (init step₁ step₂ final : Prop) (h : ¬ final) :
    ¬ ((init ∧ step₁) ∧ (step₂ ∧ final)) := by
  __veil_bmc_normalize
  guard_target =ₛ ¬ ((init ∧ step₁) ∧ (step₂ ∧ final))
  exact fun hTrace => h hTrace.2.2

set_option veil.smt.trust false in
theorem shadowed_constraints (p : Prop) (h : p) (h : ¬ p) : False := by
  __veil_bmc_check_hints
  veil_smt

/-- info: 'shadowed_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shadowed_constraints
end LogicalScopes

veil module TraceLocalNormalization

type node
relation marked : node → Bool
individual flag : Bool

#gen_state

after_init { marked N := false; flag := false }

action fill {
  let f ← pick (node → Bool)
  require ∀ n, f n
  marked N := f N
}
action clear {
  let f ← pick (node → Bool)
  require ∀ n, ¬ f n
  marked N := f N
}
action once {
  require ¬ flag
  flag := true
}
invariant True
#gen_spec

section TrustedChecks
set_option veil.smt.trust true

-- These two steps require different function witnesses.
#guard_msgs(drop info, drop warning) in
sat trace [independent_choices] {
  fill
  assert (∀ n, marked n)
  clear
  assert (∀ n, ¬ marked n)
}

#guard_msgs(drop info, drop warning) in
sat trace [alternative_choices] {
  any 3 actions
  assert (∃ n, marked n)
}

-- Both transition formulas are individually satisfiable; the shared middle
-- state makes their conjunction impossible.
#guard_msgs(drop info, drop warning) in
unsat trace [shared_middle_state] {
  once
  once
}

#guard_msgs(drop info, drop warning) in
sat trace [zero_actions] { assert (∀ n, ¬ marked n) }

#guard_msgs(drop info, drop warning) in
unsat trace [false_assertion] { assert False }

end TrustedChecks

section UntrustedChecks
set_option veil.smt.trust false

unsat trace [kernel_checked_shared_state] {
  once
  once
} by
  veil_bmc

/-- info: 'TraceLocalNormalization.kernel_checked_shared_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_checked_shared_state

-- Proof premises retain the conservative normalization path.
theorem false_proof_header : False → ¬ True := by
  veil_bmc

end UntrustedChecks
end TraceLocalNormalization
