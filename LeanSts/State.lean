import Lean
import Std.Lean.Meta.UnusedNames

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
        x := x.push (<- Lean.Elab.Term.mkFreshIdent (Lean.mkIdent "x"))
    let tuple1 <- `(term| [tupl| $is: term *])
    let tuple2 <- `(term| [tupl| $[$x: ident] * ] )
    let stx <- `(fun $[$x:ident]* => if $tuple2 = $tuple1 then $b else $f:term $x *)
    -- dbg_trace toString stx
    return stx

open Lean Expr Lean.Meta

/-- Applies functional extensionality to all equalities between functions. -/
simproc ↓ funextEq (_ = _) :=
  fun e => do
  let_expr Eq _ lhs rhs := e | return .continue
  let (lhsT, rhsT) := (← inferType lhs, ← inferType rhs)
  if lhsT.isArrow && rhsT.isArrow then
    -- NOTE: this cannot be `anonymous` because it is used in the SMT-LIB
    -- translation, which gets confused in the presence of multiple anonymous
    -- binders. TODO: generate a more informative name.
    let bn ← getUnusedUserName `a
    let bt := lhsT.bindingDomain!
    let lhs := app lhs (bvar 0)
    let rhs := app rhs (bvar 0)
    let qexpr := forallE bn bt (← mkEq lhs rhs) BinderInfo.default
    return .visit { expr := qexpr }
  return .continue

/-- Replaces equality comparison between tuples with conjunction.
  For instance, `(a, b) = (c, d)` is replaced with `a = c ∧ b = d`. -/
simproc ↓ tupleEq (_ = _) :=
  fun e => do
  let_expr Eq _ lhs rhs := e | return .continue
  if lhs.isAppOfArity `Prod.mk 4 && rhs.isAppOfArity `Prod.mk 4 then
    -- first two arguments (indices 0 and 1) are types
    let (lhs₁, lhs₂) := (lhs.getArg! 2, lhs.getArg! 3)
    let (rhs₁, rhs₂) := (rhs.getArg! 2, rhs.getArg! 3)
    let qexpr := mkAnd (← mkEq lhs₁ rhs₁) (← mkEq lhs₂ rhs₂)
    return .visit { expr := qexpr }
  return .continue
