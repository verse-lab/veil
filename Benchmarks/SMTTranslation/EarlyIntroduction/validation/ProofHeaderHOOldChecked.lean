module
public import Veil

open Lean Elab Tactic Veil in
elab_rules : tactic
  | `(tactic| veil_bmc) => do
    evalTactic (← `(tactic| veil_simp +instances only [nextSimp]))
    evalTactic (← `(tactic| veil_simp +instances only [↓ existsQuantifierSimpGuarded]))
    Veil.DesugarTacticM.runByOption (← getRef) Veil.elabVeilBmc

veil module TraceProofHeaderHO

type node
individual flag : Bool
#gen_state
after_init { flag := false }
action stay { pure () }
invariant True
#gen_spec

set_option veil.smt.trust false

unsat trace [header_unsat]
    (h : (∃ f : node → Bool, ∀ n, f n) ∨ (∃ g : node → Bool, ∀ n, ¬ g n)) {
  stay
  assert flag
} by
  veil_bmc

#print axioms header_unsat

end TraceProofHeaderHO
