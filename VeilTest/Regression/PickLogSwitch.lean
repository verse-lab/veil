module

public import Veil

/-!
The executable actions record their picks in the log only when the `LogSwitch` is on: the model
checker searches with it off, since nothing reads the log there, and recovers counterexample traces
with it on. Off, every result's log is empty; on, it lists the candidates picked on the way to the
result, in order, each shown by its `Display` and rendered as `x = v`, where `x` is what the pick
is bound to. The results themselves do not depend on the switch.

Covered: a plain pick, a constrained pick after it, a pick that a `require` filters, a pick in a
procedure whose value an action uses, a havoc in the initializer, and proof-producing picks
(single and tuple witnesses, conditional picks, and empty candidate sets).
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

/- Adding a proof must preserve both the choice's source name and the log
switch; assumptions/assertions themselves must not add synthetic choices. -/
action choose_true_proof {
  let b ← pick Bool
  require _h : b
  assert _h' : b
  assume _h'' : b
  chosen := b
}

action choose_two_proof {
  let b ← pick Bool
  let c :| _h : c ≠ b
  chosen := c
}

action choose_if_proof {
  if b : Bool :| _h : b = true then
    chosen := b
  else
    chosen := false
}

action choose_pair_proof {
  let (b, c) : Bool × Bool :| _h : b ≠ c
  chosen := b
}

-- The proof is used by a partial accessor. The choice must display the
-- original Option value, without the outer subtype or its proof.
action choose_some_proof {
  let m : Option Bool :| h : m.isSome
  chosen := m.get h
}

action choose_none_proof {
  let b : Bool :| _h : False
  chosen := b
}

action choose_if_none_proof {
  if b : Bool :| _h : False then
    chosen := b
  else
    chosen := false
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

#guard (letI : LogSwitch := ⟨false⟩; run (choose_true_proof.ext.extracted _ _)) ==
  [([], some true)]
#guard (letI : LogSwitch := ⟨true⟩; run (choose_true_proof.ext.extracted _ _)) ==
  [(["b = true"], some true)]

#guard (letI : LogSwitch := ⟨false⟩; run (choose_two_proof.ext.extracted _ _)) ==
  [([], some false), ([], some true)]
#guard (letI : LogSwitch := ⟨true⟩; run (choose_two_proof.ext.extracted _ _)) ==
  [(["b = true", "c = false"], some false), (["b = false", "c = true"], some true)]

#guard (letI : LogSwitch := ⟨false⟩; run (choose_if_proof.ext.extracted _ _)) ==
  [([], some true)]
#guard (letI : LogSwitch := ⟨true⟩; run (choose_if_proof.ext.extracted _ _)) ==
  [(["b = true"], some true)]

#guard (letI : LogSwitch := ⟨false⟩; run (choose_pair_proof.ext.extracted _ _)) ==
  [([], some true), ([], some false)]
#guard (letI : LogSwitch := ⟨true⟩; run (choose_pair_proof.ext.extracted _ _)) ==
  [(["(b, c) = (true, false)"], some true), (["(b, c) = (false, true)"], some false)]

#guard (letI : LogSwitch := ⟨false⟩; run (choose_some_proof.ext.extracted _ _)) ==
  [([], some true), ([], some false)]
#guard (letI : LogSwitch := ⟨true⟩; run (choose_some_proof.ext.extracted _ _)) ==
  [(["m = some true"], some true), (["m = some false"], some false)]

-- No candidate means no execution for a pick, or an unlogged else branch
-- for a conditional pick. The failed witness must not leave a choice behind.
#guard (letI : LogSwitch := ⟨false⟩; run (choose_none_proof.ext.extracted _ _)) == []
#guard (letI : LogSwitch := ⟨true⟩; run (choose_none_proof.ext.extracted _ _)) == []
#guard (letI : LogSwitch := ⟨false⟩; run (choose_if_none_proof.ext.extracted _ _)) ==
  [([], some false)]
#guard (letI : LogSwitch := ⟨true⟩; run (choose_if_none_proof.ext.extracted _ _)) ==
  [([], some false)]

end PickLogSwitch
