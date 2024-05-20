import Lean

declare_syntax_cat tupl
syntax term "[" (term),* " ↦ " term "]" : term
syntax (term:max)* : tupl
syntax "[tupl|" tupl "]" : term

macro_rules
  | `(term| [tupl|  $arg: term $args: term *]) => `(($arg, [tupl| $args: term *] ))
  | `(term| [tupl| ]) => `(())

def isCapital (i : Lean.Syntax) : Bool :=
  i.getId.isStr && i.getId.toString.all (fun c => c.isUpper || c.isDigit)

macro_rules
  | `(term| $f[$is:term,* ↦ $b ]) => do
    let mut x : Array $ Lean.TSyntax `ident := #[]
    for i in is.getElems do
      if isCapital i then
        x := x.push ⟨i.raw⟩
      else
        x := x.push (<- Lean.Elab.Term.mkFreshIdent (Lean.mkIdent "x"))
    let tuple1 <- `(term| [tupl| $is: term *])
    let tuple2 <- `(term| [tupl| $[$x: ident] * ] )
    let stx <- `(fun $[$x:ident]* => if $tuple2 = $tuple1 then $b else $f:term $x *)
    -- dbg_trace toString stx
    return stx

open Lean Expr Lean.Meta in
/-- This procedure applies functional extensionality to state updates.
    This is needed for translation to SMT-LIB via `lean-smt`, since
    lambdas are not supported in the SMT-LIB language.
-/
simproc ↓ funextStateUpdate (_ = (fun $[$x:ident]* => if $t2 = $t1 then $b else $f:term $x *)) :=
  fun e => do
  let_expr Eq _ old upd := e | return .continue
  match upd with -- FIXME: not sure why `let_expr` doesn't work again
  | .lam bn bt _ bi =>
    let LHS := app old (bvar 0)
    let RHS := app upd (bvar 0)
    let qexpr := forallE bn bt (← mkEq LHS RHS) bi
    return .visit { expr := qexpr }
  | _ => return .continue
