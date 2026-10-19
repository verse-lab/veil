module
public import Veil

/-!
Standalone correctness probe for the minimal issue #123 candidate: introduce
outer trace binders before calling the existing `veil_bmc` implementation.
This standalone probe installs an experimental tactic override for its checks.
Production sources are unchanged; this probe is not part of the library imports.

Run with:
  lake env lean --plugin=.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so \
    Benchmarks/SMTTranslation/EarlyIntrosChecks.lean

The actions deliberately contain a function-valued nondeterministic choice,
so this also exercises genuine higher-order existential lifting. Both named
and unconstrained action traces check SAT/UNSAT and SAT model extraction.
-/

open Lean Elab Tactic Veil in
elab_rules : tactic
  | `(tactic| veil_bmc) => do
    evalTactic (← `(tactic| veil_intros))
    Veil.DesugarTacticM.runByOption (← getRef) Veil.elabVeilBmc

veil module EarlyHOTrace

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

end UntrustedChecks

end EarlyHOTrace
