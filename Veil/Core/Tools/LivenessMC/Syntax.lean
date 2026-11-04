module

public meta import Lean
public meta import Lentil.Basic
public import Lasso.LTL.Syntax

public meta section

/-! # `[ltl| φ]`: LTL formulas as `Lasso.Formula` syntax trees

The deep counterpart of Lentil's `[tlfml| φ]`, over the same `tlfml` syntax category. What an atom means is up to the
context, a Veil module reads `⌜ t ⌝`, `Enabled …`, `⟨…⟩`, `𝒲ℱ …` and `𝒮ℱ …` against itself through
`Veil.elabModuleLtlAtom`, tried first. -/

namespace Veil.LivenessMC

open Lean Elab Term

/-- An LTL formula as an `Lasso.Formula` syntax tree. -/
syntax (name := ltlFormula) "[ltl|" tlfml "]" : term

macro_rules
  | `([ltl| ( $f )]) => `([ltl| $f])
  | `([ltl| ⊤]) => `(Lasso.Formula.tt)
  | `([ltl| ⊥]) => `(Lasso.Formula.ff)
  | `([ltl| ¬ $f]) => `(Lasso.Formula.not [ltl| $f])
  | `([ltl| □ $f]) => `(Lasso.Formula.always [ltl| $f])
  | `([ltl| ◇ $f]) => `(Lasso.Formula.eventually [ltl| $f])
  | `([ltl| ◯ $f]) => `(Lasso.Formula.next [ltl| $f])
  | `([ltl| $f ∧ $g]) => `(Lasso.Formula.and [ltl| $f] [ltl| $g])
  | `([ltl| $f ∨ $g]) => `(Lasso.Formula.or [ltl| $f] [ltl| $g])
  | `([ltl| $f → $g]) => `(Lasso.Formula.implies [ltl| $f] [ltl| $g])
  | `([ltl| $f ↔ $g]) => `(Lasso.Formula.iff [ltl| $f] [ltl| $g])
  | `([ltl| $f 𝑈 $g]) => `(Lasso.Formula.until [ltl| $f] [ltl| $g])
  | `([ltl| $f ↝ $g]) => `([ltl| □ ($f → ◇ $g)])
  | `([ltl| $f ⇒ $g]) => `([ltl| □ ($f → $g)])

/-- The atoms of `[ltl| …]` outside a Veil module, `⌜ a ⌝` is the atom `a`, and a plain term is a formula. -/
@[term_elab ltlFormula] def elabLtlAtom : TermElab := fun stx expectedType? => do
  match stx with
  | `([ltl| ⌜ $a:term ⌝]) => elabTerm (← `(Lasso.Formula.atom $a)) expectedType?
  | `([ltl| $t:term]) => elabTerm t expectedType?
  | `([ltl| $f]) => throwErrorAt f "`[ltl| …]` has no counterpart for this formula"
  | _ => throwUnsupportedSyntax

end Veil.LivenessMC
