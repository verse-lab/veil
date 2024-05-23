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

theorem funextEq {α β : Type} (f g : α → β) :
  (f = g) = ∀ x, f x = g x := by
  apply propext
  constructor
  { intro h ; simp only [h, implies_true] }
  { intro h ; apply funext h }

theorem tupleEq [DecidableEq t1] [DecidableEq t2] (a c : t1) (b d : t2):
  ((a, b) = (c, d)) = (a = c ∧ b = d) := by
  apply propext
  constructor
  { intro h ; injection h ; constructor <;> assumption }
  { rintro ⟨h1, h2⟩ ; rw [h1, h2] }
