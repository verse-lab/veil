module
public import Veil
public section
set_option veil.experimental.bmcCache true

-- The internal helper consumes simp syntax through mkSimpContext, not evalTactic.
set_option linter.unreachableTactic false

/-! Semantic regressions for exact cached transition normalization. The manual theorems
below are kernel checked; SAT commands also exercise trace model decoding. -/

namespace CacheLogicalScopes
open Lean Elab Tactic

-- An inactive branch with an empty witness domain must stay satisfiable.
theorem inactive_empty_witness :
    ¬¬ (True ∨ (∃ _f : Unit → Empty, True)) := by
  __veil_bmc_split_trace
  __veil_bmc_hyps simp (failIfUnchanged := false) only [↓ Veil.existsQuantifierSimpGuarded]
  exact bmc_clause_0 trivial

-- Quantifier dependence cannot be exchanged even when both types are inhabited.
theorem dependent_choice_scope :
    (∀ x : Bool, ∃ f : Unit → Bool, f () = x) ∧
    ¬ (∃ f : Unit → Bool, ∀ x : Bool, f () = x) := by
  constructor
  · intro x; exact ⟨fun _ => x, rfl⟩
  · __veil_bmc_split_trace
    __veil_bmc_hyps simp (failIfUnchanged := false) only [↓ Veil.existsQuantifierSimpGuarded]
    rcases bmc_clause_0 with ⟨f, h⟩
    have := (h true).symm.trans (h false)
    contradiction

-- Distinct witnesses survive splitting, and dependent witness types stay scoped.
theorem independent_and_dependent_witnesses :
    ¬ (((∃ f : Unit → Bool, f () = true) ∧ (∃ g : Unit → Bool, g () = false)) ∧
        (∀ f : Unit → Bool, f () = true)) := by
  __veil_bmc_split_trace
  __veil_bmc_hyps simp (failIfUnchanged := false) only [↓ Veil.existsQuantifierSimpGuarded]
  rcases bmc_clause_1 with ⟨g, hg⟩
  have := (bmc_clause_2 g).symm.trans hg
  contradiction

theorem dependent_witness_type :
    ¬ ((∃ n : Nat, ∃ w : Fin (n + 1), w.val > n) ∧ True) := by
  __veil_bmc_split_trace
  __veil_bmc_hyps simp (failIfUnchanged := false) only [↓ Veil.existsQuantifierSimpGuarded]
  rcases bmc_clause_0 with ⟨n, w, h⟩
  omega

set_option veil.smt.trust false in
theorem shadowed_constraints (p : Prop) (h : p) (h : ¬ p) : False := by
  __veil_bmc_check_hints
  veil_smt

/-- info: 'CacheLogicalScopes.shadowed_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shadowed_constraints
end CacheLogicalScopes

veil module TraceCachedNormalization

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

-- Inspect the actual artifacts as well as solver results. The normal forms
-- are kernel theorems; neither a trusted SMT result nor an admitted proof may
-- be used to construct them.
open Lean Elab Command in
run_cmd do
  for name in [``__bmc_init_eq, ``__bmc_any_eq, ``__bmc_action.fill.eq] do
    if (← collectAxioms name).contains ``sorryAx then
      throwError "cached equality uses sorryAx: {name}"

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

/-- info: 'TraceCachedNormalization.kernel_checked_shared_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_checked_shared_state

unsat trace [false_proof_header] (_h : False) { fill } by
  veil_bmc

end UntrustedChecks
end TraceCachedNormalization


-- Template-local binders must not capture module sorts with common names.
veil module TraceCacheBinderNames
type pre
type post
type tag
individual flag : Bool
#gen_state
after_init { flag := false }
action enable (x : pre) (y : post) { flag := true }
action disable { flag := false }
invariant True
#gen_spec

#guard_msgs (drop info, drop warning) in
sat trace {
  enable
  assert flag
}

#guard_msgs (drop info, drop warning) in
sat trace {
  any action
  assert flag
}

#guard_msgs (drop info, drop warning) in
unsat trace {
  enable
  disable
  assert flag
}
end TraceCacheBinderNames
