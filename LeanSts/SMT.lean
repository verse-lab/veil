import LeanSts.State
import Auto
set_option auto.smt true
set_option trace.auto.printLemmas true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.lamFOL2SMT true

section SMT
structure TotalOrder (t : Type) :=
  -- relation: total order
  le (x y : t) : Bool
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x

open Lean Elab Tactic
syntax (name := gen_smt) "gen_smt" term : tactic

set_option trace.gen_smt true


@[tactic gen_smt]
def evalGenSMT : Tactic
| `(gen_smt | gen_smt $term) => withMainContext do
  trace[gen_smt] s!"{term}"
  let expr ← elabTerm term none false
  trace[gen_smt] s!"{expr}"
| _ => throwUnsupportedSyntax

example : True := by
  gen_smt (TotalOrder (Fin 5))
  exact True.intro
end SMT
