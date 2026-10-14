module

public import Veil

/-! `WF(a)` and `SF(a)` abbreviate the fairness conditions `(◇ □ E(a)) → □ ◇ T(a)` and
`(□ ◇ E(a)) → □ ◇ T(a)`, and only exist for model checking. -/

veil module TemporalFairness

abbrev Loc := Fin 3
individual loc : Loc

after_init { loc := (0 : Loc) }

-- From the hub `0` one steps to a leaf, where one can stay or step back. Each `toLeaf l` is enabled at
-- the hub only, so weak fairness never forces it, while strong fairness does once the hub keeps coming back.
action toLeaf (l : Loc) {
  require loc = (0 : Loc) ∧ l ≠ (0 : Loc)
  loc := l
}
action toHub {
  require loc ≠ (0 : Loc)
  loc := (0 : Loc)
}
action stay {
  require loc ≠ (0 : Loc)
  loc := loc
}

-- HOLDS: a run that stays at a leaf forever is unfair to `toHub`
temporal (only := check) [weakHolds] WF(toHub) → □ ◇ ⌜ loc = (0 : Loc) ⌝
temporal (only := check) [weakHoldsByHand] ((◇ □ E(toHub)) → □ ◇ T(toHub)) → □ ◇ ⌜ loc = (0 : Loc) ⌝
-- FAILS: the run `0, 2, 0, 2, …` is weakly fair to `toLeaf 1`, which it disables at every leaf
temporal (only := check) [weakFails] WF(toLeaf 1) ∧ WF(toHub) → ◇ ⌜ loc = (1 : Loc) ⌝
-- HOLDS: the same run is not strongly fair to `toLeaf 1`
temporal (only := check) [strongHolds] SF(toLeaf 1) ∧ WF(toHub) → ◇ ⌜ loc = (1 : Loc) ⌝
temporal (only := check) [strongHoldsByHand]
  ((□ ◇ E(toLeaf 1)) → □ ◇ T(toLeaf 1)) ∧ ((◇ □ E(toHub)) → □ ◇ T(toHub)) → ◇ ⌜ loc = (1 : Loc) ⌝
-- FAILS: it is strongly fair to `toLeaf` as a whole, since it takes `toLeaf 2` at every visit of the hub
temporal (only := check) [strongWholeFails] SF(toLeaf) ∧ WF(toHub) → ◇ ⌜ loc = (1 : Loc) ⌝

#gen_spec

-- The abbreviations elaborate to the formulas written out
open Lean in
run_meta do
  let formulaOf (n : Name) : MetaM Expr := do
    let some e := (← getConstInfo n).value!.find? (·.isAppOf ``Veil.LivenessMC.LivenessProperty.ofFormula)
      | throwError "{n} is not built by `LivenessProperty.ofFormula`"
    return e.appArg!
  for (sugar, byHand) in [(``TemporalFairness.weakHolds.ast, ``TemporalFairness.weakHoldsByHand.ast),
      (``TemporalFairness.strongHolds.ast, ``TemporalFairness.strongHoldsByHand.ast)] do
    unless (← formulaOf sugar) == (← formulaOf byHand) do
      throwError "{sugar} and {byHand} have different formulas"

/-- info: ✅ No liveness violation (checked 1 properties, explored 6 product states) -/
#guard_msgs in
#liveness_check [weakHolds] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 6 product states) -/
#guard_msgs in
#liveness_check [weakHoldsByHand] interpreted {}
/-- error: ❌ Violation: liveness_failure (violates: weakFails) -/
#guard_msgs (substring := true) in
#liveness_check [weakFails] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 5 product states) -/
#guard_msgs in
#liveness_check [strongHolds] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 5 product states) -/
#guard_msgs in
#liveness_check [strongHoldsByHand] interpreted {}
/-- error: ❌ Violation: liveness_failure (violates: strongWholeFails) -/
#guard_msgs (substring := true) in
#liveness_check [strongWholeFails] interpreted {}

/-- error: unknown action `toLeave`; the module's actions are [toLeaf, toHub, stay] -/
#guard_msgs in
temporal (only := check) [unknownAction] SF(toLeave)

/--
error: action `toLeaf` takes 1 parameter(s), but 2 were given; write `toLeaf` on its own for any instantiation
-/
#guard_msgs in
temporal (only := check) [tooManyArguments] WF(toLeaf 1 2)

/--
warning: `strongDegraded` is only model checked, since its proof definition fails to elaborate (write `temporal (only := check)` to say so):
  `SF(…)` only exists for model checking
-/
#guard_msgs in
temporal [strongDegraded] SF(toLeaf 1) → ◇ ⌜ loc = (1 : Loc) ⌝

/-- error: `WF(…)` only exists for model checking -/
#guard_msgs in
temporal (only := verify) [weakProved] WF(toHub) → □ ◇ ⌜ loc = (0 : Loc) ⌝

end TemporalFairness
