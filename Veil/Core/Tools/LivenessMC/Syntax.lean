module

public meta import Lean
public meta import Lentil.Basic
public import LTLLib.LTL.Syntax

public meta section

/-! # `[ltl| φ]`: LTL formulas as `LTLLib.Formula` syntax trees

The deep counterpart of Lentil's `[tlfml| φ]`, over the same `tlfml` syntax category. The connectives
are macros onto the constructors of `LTLLib.Formula`. What an atom means is up to the context: here
`⌜ a ⌝` is the atom `a` itself and a plain term is a formula, while a Veil module reads `⌜ t ⌝`,
`E(…)` and `T(…)` against itself through an elaborator of its own (`Veil.elabModuleLtlAtom`), which,
registered later, is tried first. -/

namespace Veil.LivenessMC

open Lean Elab Term

/-- `φ ↔ ψ`. Non-associative, like Lean's `↔`. -/
syntax:20 (name := tlfmlIff) tlfml:21 " ↔ " tlfml:21 : tlfml

/-- An LTL formula as an `LTLLib.Formula` syntax tree. -/
syntax (name := ltlFormula) "[ltl|" tlfml "]" : term

macro_rules
  | `([ltl| ( $f )]) => `([ltl| $f])
  | `([ltl| ⊤]) => `(LTLLib.Formula.tt)
  | `([ltl| ⊥]) => `(LTLLib.Formula.ff)
  | `([ltl| ¬ $f]) => `(LTLLib.Formula.not [ltl| $f])
  | `([ltl| □ $f]) => `(LTLLib.Formula.always [ltl| $f])
  | `([ltl| ◇ $f]) => `(LTLLib.Formula.eventually [ltl| $f])
  | `([ltl| ◯ $f]) => `(LTLLib.Formula.next [ltl| $f])
  | `([ltl| $f ∧ $g]) => `(LTLLib.Formula.and [ltl| $f] [ltl| $g])
  | `([ltl| $f ∨ $g]) => `(LTLLib.Formula.or [ltl| $f] [ltl| $g])
  | `([ltl| $f → $g]) => `(LTLLib.Formula.implies [ltl| $f] [ltl| $g])
  | `([ltl| $f ↔ $g]) => `(LTLLib.Formula.iff [ltl| $f] [ltl| $g])
  | `([ltl| $f 𝑈 $g]) => `(LTLLib.Formula.until [ltl| $f] [ltl| $g])
  | `([ltl| $f ↝ $g]) => `([ltl| □ ($f → ◇ $g)])
  | `([ltl| $f ⇒ $g]) => `([ltl| □ ($f → $g)])

/-- The atoms of `[ltl| …]` outside a Veil module: `⌜ a ⌝` is the atom `a`, and a plain term is a
formula. -/
@[term_elab ltlFormula] def elabLtlAtom : TermElab := fun stx expectedType? => do
  match stx with
  | `([ltl| ⌜ $a:term ⌝]) => elabTerm (← `(LTLLib.Formula.atom $a)) expectedType?
  | `([ltl| $t:term]) => elabTerm t expectedType?
  | `([ltl| $f]) => throwErrorAt f "`[ltl| …]` has no counterpart for this formula"
  | _ => throwUnsupportedSyntax

end Veil.LivenessMC
