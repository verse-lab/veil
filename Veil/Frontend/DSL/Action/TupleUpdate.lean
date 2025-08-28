import Lean
import Veil.Util.Meta
open Lean Elab Command Term Meta Lean.Parser

namespace Veil

/-- Syntax for assigning only a sub-part of a relation / function, e.g.
`r N x ↦ True`. -/
syntax term "[" (term),* " ↦ " term "]" : term
declare_syntax_cat veil_tupl
scoped syntax (term:max)* : veil_tupl
scoped syntax (name := veil_tupl) "[veil_tupl|" veil_tupl "]" : term

@[term_elab veil_tupl]
def veil_tuplElab : TermElab := fun stx type? => do
  match stx with
  | `(term| [veil_tupl| $arg: term $args: term *]) =>
    let newStx ← if args.size == 0 then `($arg) else `(($arg, [veil_tupl| $args: term *]))
    elabTerm newStx type?
  | _ => throwUnsupportedSyntax

macro_rules
  | `(term| $f[$is:term,* ↦ $b ]) => do
    let mut x : Array $ Lean.TSyntax `ident := #[]
    for i in is.getElems do
      if isCapital i.raw.getId && x.all (· != ⟨i.raw⟩) then
        x := x.push ⟨i.raw⟩
      else
        x := x.push (<- Lean.Elab.Term.mkFreshIdent i)
    let tuple1 <- `(term| [veil_tupl| $is: term *])
    let tuple2 <- `(term| [veil_tupl| $[$x: ident] * ] )
    let stx <- `(fun $[$x:ident]* => if $tuple2 = $tuple1 then $b else $f:term $x *)
    -- dbg_trace toString stx
    return stx

end Veil
