module

public import Veil

/-!
Each pick is logged under what it is bound to, as `x = v`. `TraceChoices` and `PickLogSwitch`
cover `let x ← pick τ`, `let x :| p`, picks in procedures and a havoc of an individual; here are the
other ways to bind a pick: a pattern, `veil_var`, an arrow assignment to a state component, havocs
of relations, the witness of an existential `if`, and `veil_let`, which is a pick with a single
candidate.

A havoc with universal indices picks a function of them, shown as a set, so it is named by that
function rather than by the target as written: `r N := *` by `r`, `q a X := *` by `q a`, and
`q X a := *` by `q · a`. A havoc at a point is named by the target, `r n`.
-/

veil module PickNames

individual chosen : Bool
relation r : Bool → Bool
relation q : Bool → Bool → Bool

#gen_state

after_init {
  chosen := false
  r N := false
  q X Y := false
}

action pattern_bind {
  let (a, _) ← pick (Bool × Bool)
  chosen := a
}

action var_pick {
  veil_var v : Bool
  chosen := v
}

action assign_state {
  chosen ← pick Bool
}

action havoc_point (n : Bool) {
  r n := *
}

action havoc_all {
  r N := *
}

action havoc_row (a : Bool) {
  q a X := *
}

action havoc_column (a : Bool) {
  q X a := *
}

action if_some {
  if y :| y = true then
    chosen := y
}

action logical_let {
  veil_let z := !chosen
  chosen := z
}

invariant true

#gen_spec

#gen_executable

def initial : State FieldConcreteType := { chosen := false, r := default, q := default }

/-- The logs of the results of `act` from `initial`, rendered. -/
def logs (act : VeilMultiExecM Std.Format Int Theory (State FieldConcreteType) PUnit) :
    List (List String) :=
  (act {} initial).map fun (log, _) => log.map toString

#guard (letI : LogSwitch := ⟨true⟩; logs (pattern_bind.ext.extracted _ _)) ==
  [["(a, _) = (true, true)"], ["(a, _) = (true, false)"], ["(a, _) = (false, true)"],
   ["(a, _) = (false, false)"]]

#guard (letI : LogSwitch := ⟨true⟩; logs (var_pick.ext.extracted _ _)) ==
  [["v = true"], ["v = false"]]

#guard (letI : LogSwitch := ⟨true⟩; logs (assign_state.ext.extracted _ _)) ==
  [["chosen = true"], ["chosen = false"]]

#guard (letI : LogSwitch := ⟨true⟩; logs (havoc_point.ext.extracted _ _ true)) ==
  [["r n = true"], ["r n = false"]]

#guard (letI : LogSwitch := ⟨true⟩; logs (havoc_all.ext.extracted _ _)) ==
  [["r = {true, false}"], ["r = {true}"], ["r = {false}"], ["r = {}"]]

#guard (letI : LogSwitch := ⟨true⟩; logs (havoc_row.ext.extracted _ _ true)) ==
  [["q a = {true, false}"], ["q a = {true}"], ["q a = {false}"], ["q a = {}"]]

#guard (letI : LogSwitch := ⟨true⟩; logs (havoc_column.ext.extracted _ _ true)) ==
  [["q · a = {true, false}"], ["q · a = {true}"], ["q · a = {false}"], ["q · a = {}"]]

#guard (letI : LogSwitch := ⟨true⟩; logs (if_some.ext.extracted _ _)) == [["y = true"]]

#guard (letI : LogSwitch := ⟨true⟩; logs (logical_let.ext.extracted _ _)) == [["z = true"]]

end PickNames
