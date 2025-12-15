import Lean
import Veil.Util.Meta
open Lean Elab Command Term Meta Lean.Parser

namespace Veil

/-- Syntax for assigning only a sub-part of a relation / function, e.g.
`r N x ↦ True`. -/
syntax term "_[" (term),* " ↦ " term "]_" : term
declare_syntax_cat veil_tupl
scoped syntax (term:max)* : veil_tupl
scoped syntax (name := veil_tupl) "_[veil_tupl|" veil_tupl "]_" : term

@[term_elab veil_tupl]
def veil_tuplElab : TermElab := fun stx type? => do
  match stx with
  | `(term| _[veil_tupl| $arg: term $args: term *]_) =>
    let newStx ← if args.size == 0 then `($arg) else `(($arg, _[veil_tupl| $args: term *]_))
    elabTerm newStx type?
  | _ => throwUnsupportedSyntax

def TupleUpdate.findFirstAppearance [Monad m] [MonadQuotation m] (arr : Array (TSyntax `term)) (base : Array (TSyntax `term) := #[]) :
  m (Array (Ident × Option Nat)) := do
  let mut res : Array (Ident × Option Nat) := #[]
  let mut x := base
  for i in arr do
    if isCapital i.raw.getId then
      let n := x.findIdx? (· == ⟨i.raw⟩)
      match n with
      | some idx =>
        let i' ← Lean.Elab.Term.mkFreshIdent i
        res := res.push (i', some idx)
        x := x.push i'
      | none =>
        res := res.push (⟨i.raw⟩, none)
        x := x.push ⟨i.raw⟩
    else
      let i' ← Lean.Elab.Term.mkFreshIdent i
      res := res.push (i', none)
      x := x.push i'
  return res

macro_rules
  | `(term| $f _[$is:term,* ↦ $b ]_) => do
    let x ← TupleUpdate.findFirstAppearance is.getElems
    let x := x.map Prod.fst
    let tuple1 <- `(term| _[veil_tupl| $is: term *]_)
    let tuple2 <- `(term| _[veil_tupl| $[$x: ident] * ]_ )
    let body ← `(if $tuple2 = $tuple1 then $b else $f:term $x *)
    let stx <- mkFunSyntax x body
    -- dbg_trace toString stx
    return stx

end Veil
