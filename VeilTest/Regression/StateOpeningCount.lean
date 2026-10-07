module

public import Veil

/-!
# Regression: one state opening per program point

Every statement of a Veil action opens the current state once
(`__veil_state✝ ← get`, see `openStateAround`), and the right-hand side of an
arrow assignment, the pick of a havoc, and the pick of `let x :| p` are all
elaborated *under* that opening instead of opening the state again. An
opening is exactly one `get` in the elaborated `.do` term, so this test pins
the number of `get`s per statement kind. A count that grows means a handler
started opening the state twice for the same program point; every opening
binds views of the state's fields, so this also multiplies elaboration cost.

The last section pins the number of `let`s an opening leaves behind, which
shows that each opened field is bound once and that writes read the state
directly.
-/

set_option linter.unusedVariables false

open Lean in
meta partial def countGets (e : Expr) : Nat := Id.run do
  let here := match e with
    | .const c _ => if [``MonadStateOf.get, ``MonadState.get, ``getThe].contains c then 1 else 0
    | _ => 0
  e.foldlM (init := here) fun n child => pure (n + countGets child)

open Lean Elab Command in
/-- `#count_gets act.do` reports the number of `get`s in the value of `act.do`. -/
elab "#count_gets " id:ident : command => liftTermElabM do
  let n ← resolveGlobalConstNoOverload id
  let ci ← getConstInfoDefn n
  logInfo m!"{id.getId}: {countGets ci.value}"

open Lean in
meta partial def countLets (e : Expr) : Nat := Id.run do
  let here := if e.isLet then 1 else 0
  e.foldlM (init := here) fun n child => pure (n + countLets child)

open Lean Elab Command in
/-- `#count_lets act.do` reports the number of `let`s in the value of `act.do`. -/
elab "#count_lets " id:ident : command => liftTermElabM do
  let n ← resolveGlobalConstNoOverload id
  let ci ← getConstInfoDefn n
  logInfo m!"{id.getId}: {countLets ci.value}"

veil module StateOpeningCount

individual x : Bool
individual y : Nat
relation r : Bool → Bool

#gen_state

procedure ret_nat { return (1 : Nat) }
procedure ret_bool { return true }
procedure unit_act { x := true }

/-! ## One statement, one opening -/

procedure plain_assign { x := true }
/-- info: plain_assign.do: 1 -/
#guard_msgs in #count_gets plain_assign.do

procedure indexed_assign { r true := true }
/-- info: indexed_assign.do: 1 -/
#guard_msgs in #count_gets indexed_assign.do

procedure havoc { x := * }
/-- info: havoc.do: 1 -/
#guard_msgs in #count_gets havoc.do

procedure indexed_havoc { r true := * }
/-- info: indexed_havoc.do: 1 -/
#guard_msgs in #count_gets indexed_havoc.do

procedure let_arrow { let v ← ret_nat }
/-- info: let_arrow.do: 1 -/
#guard_msgs in #count_gets let_arrow.do

procedure let_pick { let v ← pick Nat }
/-- info: let_pick.do: 1 -/
#guard_msgs in #count_gets let_pick.do

procedure pick_such_that { let v :| v = (1 : Nat) }
/-- info: pick_such_that.do: 1 -/
#guard_msgs in #count_gets pick_such_that.do

procedure pure_let { let v := 5 }
/-- info: pure_let.do: 1 -/
#guard_msgs in #count_gets pure_let.do

procedure require_stmt { require x }
/-- info: require_stmt.do: 1 -/
#guard_msgs in #count_gets require_stmt.do

procedure assert_stmt { assert x }
/-- info: assert_stmt.do: 1 -/
#guard_msgs in #count_gets assert_stmt.do

procedure call_stmt { unit_act }
/-- info: call_stmt.do: 1 -/
#guard_msgs in #count_gets call_stmt.do

procedure return_stmt { return x }
/-- info: return_stmt.do: 1 -/
#guard_msgs in #count_gets return_stmt.do

/-! ## Arrow assignments: pre-call state for the call, post-call state for
the write -/

procedure arrow_assign { y ← ret_nat }
/-- info: arrow_assign.do: 2 -/
#guard_msgs in #count_gets arrow_assign.do

procedure indexed_arrow_assign { r true ← ret_bool }
/-- info: indexed_arrow_assign.do: 2 -/
#guard_msgs in #count_gets indexed_arrow_assign.do

/-! ## Several statements: one opening each -/

procedure branch { if x then y := 1 }
/-- info: branch.do: 2 -/
#guard_msgs in #count_gets branch.do

procedure local_arrow {
  let mut v := 0
  v ← ret_nat
  return v
}
/-- info: local_arrow.do: 3 -/
#guard_msgs in #count_gets local_arrow.do

procedure uninitialized_local {
  veil_var v : Nat
  return v
}
/-- info: uninitialized_local.do: 2 -/
#guard_msgs in #count_gets uninitialized_local.do

/-! ## Pattern binders

Lean desugars `pat ← e` and `let pat ← e` into a bind of a fresh variable
followed by a separate destructuring statement, `pat := __x` or
`let pat := __x`, which Veil elaborates as a statement of its own, with its
own opening. These counts are one above the number of source statements. -/

procedure pattern_arrow {
  let mut a := 0
  let mut b := 0
  (a, b) ← pure (1, 2)
  return a + b
}
/-- info: pattern_arrow.do: 5 -/
#guard_msgs in #count_gets pattern_arrow.do

procedure pattern_pick {
  let (a, b) :| a + b = (3 : Nat)
  return a
}
/-- info: pattern_pick.do: 3 -/
#guard_msgs in #count_gets pattern_pick.do

/-! ## One `let` per opened field

An opening binds the state once (`__veil_state ← get`) and each opened field
once, as `let X := (χ_rep _).get __veil_state.X`; a write reads the value it
updates from `__veil_state.X` directly. These count the `let`s left in `.do`
after unused ones are erased. A read keeps its field view and the user's
`let`; a write keeps only the binding of the field's new value. With the
former three-binding views (`__veil_X_conc`, `__veil_X`, `X`), these counts
were 4 and 2. -/

procedure read_field {
  let v := x
  return v
}
/-- info: read_field.do: 2 -/
#guard_msgs in #count_lets read_field.do

procedure write_field { x := true }
/-- info: write_field.do: 1 -/
#guard_msgs in #count_lets write_field.do

end StateOpeningCount
