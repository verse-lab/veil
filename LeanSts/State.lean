import Lean

@[simp] abbrev updateFn [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  λ (x : α) => if x = a then b else f x

declare_syntax_cat tupl
syntax term "[" (term),* " ↦ " term "]" : term
syntax (term:max)* : tupl
syntax "[tupl|" tupl "]" : term

macro_rules
  | `(term| [tupl|  $arg: term $args: term *]) => `(($arg, [tupl| $args: term *] ))
  | `(term| [tupl| ]) => `(())


macro_rules
  | `(term| $f[$is:term,* ↦ $b ]) => do
    let mut x := #[]
    for _ in is.getElems do
      x := x.push (<- Lean.Elab.Term.mkFreshIdent (Lean.mkIdent "x"))
    let tuple1 <- `(term| [tupl| $is: term *])
    let tuple2 <- `(term| [tupl| $[$x: ident] * ] )
    `(fun $[$x:ident]* => if $tuple2 = $tuple1 then $b else $f:term $x *)
