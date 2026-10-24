module

public import Veil

/-!
The executable actions record their picks in the log only when the `LogSwitch` is on: the model
checker searches with it off, since nothing reads the log there, and recovers counterexample traces
with it on. Off, every result's log is empty; on, it lists the candidates picked on the way to the
result, in order, each shown by its `Display` and rendered as `x = v`, where `x` is what the pick
is bound to. The results themselves do not depend on the switch.

Covered: a plain pick, a constrained pick after it, a pick that a `require` filters, a pick in a
procedure whose value an action uses, and a havoc in the initializer.
-/

veil module PickLogSwitch

individual chosen : Bool

#gen_state

after_init {
  chosen := *
}

action choose {
  let b ← pick Bool
  chosen := b
}

action choose_two {
  let b ← pick Bool
  let c :| c ≠ b
  chosen := c
}

action choose_true {
  let b ← pick Bool
  require b
  chosen := b
}

procedure pick_val {
  let b ← pick Bool
  return b
}

action choose_via_procedure {
  let b ← pick_val
  chosen := b
}

invariant true

#gen_spec

#gen_executable

def initial : State FieldConcreteType := { chosen := false }

/-- For each result of `act` from `initial`: its log, rendered, and the new value of `chosen`. -/
def run (act : VeilMultiExecM Choice Int Theory (State FieldConcreteType) PUnit) :
    List (List String × Option Bool) :=
  (act {} initial).map fun (log, r) => (log.map toString, match r with
    | .res (.ok _, s) => some s.chosen
    | _ => none)

/-- The results of the initializer and of each action, with the switch set to `on`. -/
def outcomes (on : Bool) : List (List (List String × Option Bool)) :=
  letI : LogSwitch := ⟨on⟩
  [run (initializer.ext.extracted _ _), run (choose.ext.extracted _ _), run (choose_two.ext.extracted _ _),
   run (choose_true.ext.extracted _ _), run (choose_via_procedure.ext.extracted _ _)]

-- Off: no log
#guard outcomes false == [
  [([], some true), ([], some false)],
  [([], some true), ([], some false)],
  [([], some false), ([], some true)],
  [([], some true)],
  [([], some true), ([], some false)]]

-- On: the candidates picked, in order, under their names; the same results
#guard outcomes true == [
  [(["chosen = true"], some true), (["chosen = false"], some false)],
  [(["b = true"], some true), (["b = false"], some false)],
  [(["b = true", "c = false"], some false), (["b = false", "c = true"], some true)],
  [(["b = true"], some true)],
  [(["b = true"], some true), (["b = false"], some false)]]

end PickLogSwitch
