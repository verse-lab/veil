module

public import Veil

/-!
Introducing trace binders before normalization must preserve both SAT and UNSAT
results, including actions with function-valued nondeterministic choices.
These checks exercise the production `veil_bmc` tactic without an override.
-/

veil module TraceEarlyIntroduction

type node
relation marked : node → Bool

after_init { marked N := false }

action fill {
  let f ← pick (node → Bool)
  require ∀ n, f n
  marked N := f N
}

action clear { marked N := false }

invariant True

#gen_spec

section TrustedChecks

set_option veil.smt.trust true

-- A real higher-order choice must remain available to the solver.
#guard_msgs(drop info, drop warning) in
sat trace [fill_all] {
  fill
  assert (∀ n, marked n)
}

#guard_msgs(drop info, drop warning) in
unsat trace [fill_cannot_leave_unmarked] {
  fill
  assert (∃ n, ¬ marked n)
}

#guard_msgs(drop info, drop warning) in
sat trace [choose_fill] {
  any 3 actions
  assert (∃ n, marked n)
}

#guard_msgs(drop info, drop warning) in
unsat trace [always_uniform] {
  any 3 actions
  assert ((∃ n, marked n) ∧ (∃ n, ¬ marked n))
}

end TrustedChecks

-- Repeat with proof reconstruction enabled for UNSAT results.
section UntrustedChecks

set_option veil.smt.trust false

#guard_msgs(drop info, drop warning) in
sat trace [fill_all_untrusted] {
  fill
  assert (∀ n, marked n)
}

#guard_msgs(drop info, drop warning) in
unsat trace [fill_cannot_leave_unmarked_untrusted] {
  fill
  assert (∃ n, ¬ marked n)
}

#guard_msgs(drop info, drop warning) in
sat trace [choose_fill_untrusted] {
  any 3 actions
  assert (∃ n, marked n)
}

#guard_msgs(drop info, drop warning) in
unsat trace [always_uniform_untrusted] {
  any 3 actions
  assert ((∃ n, marked n) ∧ (∃ n, ¬ marked n))
}

-- A manual trace proof must close every goal. The automatic trace discharger
-- can report an SMT result without retaining a complete Lean proof.
unsat trace [fill_cannot_leave_unmarked_checked] {
  fill
  assert (∃ n, ¬ marked n)
} by
  veil_bmc

/-- info: 'TraceEarlyIntroduction.fill_cannot_leave_unmarked_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fill_cannot_leave_unmarked_checked

end UntrustedChecks

end TraceEarlyIntroduction

/-!
Proof-valued trace binders must stay in the goal until normalization processes
their domains. Introducing this header too early leaves higher-order
existentials in a context hypothesis, which the SMT translator cannot encode.
This UNSAT query worked before early introduction and must remain supported.
-/
veil module TraceEarlyIntroductionProofHeader

type node
individual flag : Bool

#gen_state

after_init { flag := false }
action stay { pure () }
invariant True

#gen_spec

set_option veil.smt.trust false

unsat trace [preserves_higher_order_proof_header]
    (_h : (∃ f : node → Bool, ∀ n, f n) ∨ (∃ g : node → Bool, ∀ n, ¬ g n)) {
  stay
  assert flag
} by
  veil_bmc

/-- info: 'TraceEarlyIntroductionProofHeader.preserves_higher_order_proof_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms preserves_higher_order_proof_header

end TraceEarlyIntroductionProofHeader
