import Lean

declare_syntax_cat tupl
syntax term "[" (term),* " ↦ " term "]" : term
syntax (term:max)* : tupl
syntax (name := tupl) "[tupl|" tupl "]" : term

open Lean Elab Term
@[term_elab tupl]
def tuplElab : TermElab := fun stx type? => do
  match stx with
  | `(term| [tupl| $arg: term $args: term *]) =>
    let newStx ← if args.size == 0 then `($arg) else `(($arg, [tupl| $args: term *]))
    elabTerm newStx type?
  | _ => throwUnsupportedSyntax

def isCapital (i : Lean.Syntax) : Bool :=
  i.getId.isStr && i.getId.toString.all (fun c => c.isUpper || c.isDigit)

macro_rules
  | `(term| $f[$is:term,* ↦ $b ]) => do
    let mut x : Array $ Lean.TSyntax `ident := #[]
    for i in is.getElems do
      if isCapital i then
        x := x.push ⟨i.raw⟩
      else
        x := x.push (<- Lean.Elab.Term.mkFreshIdent (Lean.mkIdent `x))
    let tuple1 <- `(term| [tupl| $is: term *])
    let tuple2 <- `(term| [tupl| $[$x: ident] * ] )
    let stx <- `(fun $[$x:ident]* => if $tuple2 = $tuple1 then $b else $f:term $x *)
    -- dbg_trace toString stx
    return stx
