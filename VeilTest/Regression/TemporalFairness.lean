module

public import Veil
public import Veil.Liveness

/-! `𝒲ℱ a` and `𝒮ℱ a` are Lentil's weak and strong fairness. For model checking, they unfold to
`(◇ □ Enabled a) → □ ◇ ⟨a⟩` and `(□ ◇ Enabled a) → □ ◇ ⟨a⟩`. -/

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
temporal (only := check) [weakHolds] 𝒲ℱ toHub → □ ◇ ⌜ loc = (0 : Loc) ⌝
temporal (only := check) [weakHoldsByHand] ((◇ □ Enabled toHub) → □ ◇ ⟨toHub⟩) → □ ◇ ⌜ loc = (0 : Loc) ⌝
-- FAILS: the run `0, 2, 0, 2, …` is weakly fair to `toLeaf 1`, which it disables at every leaf
temporal (only := check) [weakFails] 𝒲ℱ (toLeaf 1) ∧ 𝒲ℱ toHub → ◇ ⌜ loc = (1 : Loc) ⌝
-- HOLDS: the same run is not strongly fair to `toLeaf 1`
temporal (only := check) [strongHolds] 𝒮ℱ (toLeaf 1) ∧ 𝒲ℱ toHub → ◇ ⌜ loc = (1 : Loc) ⌝
temporal (only := check) [strongHoldsByHand]
  ((□ ◇ Enabled (toLeaf 1)) → □ ◇ ⟨toLeaf 1⟩) ∧ ((◇ □ Enabled toHub) → □ ◇ ⟨toHub⟩) → ◇ ⌜ loc = (1 : Loc) ⌝
-- FAILS: it is strongly fair to `toLeaf` as a whole, since it takes `toLeaf 2` at every visit of the hub
temporal (only := check) [strongWholeFails] 𝒮ℱ toLeaf ∧ 𝒲ℱ toHub → ◇ ⌜ loc = (1 : Loc) ⌝

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
#temporal_check [weakHolds] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 6 product states) -/
#guard_msgs in
#temporal_check [weakHoldsByHand] interpreted {}
/-- error: ❌ Violation: liveness_failure (violates: weakFails) -/
#guard_msgs (substring := true) in
#temporal_check [weakFails] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 5 product states) -/
#guard_msgs in
#temporal_check [strongHolds] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 5 product states) -/
#guard_msgs in
#temporal_check [strongHoldsByHand] interpreted {}
/-- error: ❌ Violation: liveness_failure (violates: strongWholeFails) -/
#guard_msgs (substring := true) in
#temporal_check [strongWholeFails] interpreted {}

/-- error: unknown action `toLeave`; the module's actions are [toLeaf, toHub, stay] -/
#guard_msgs in
temporal (only := check) [unknownAction] 𝒮ℱ toLeave

/--
error: action `toLeaf` takes 1 parameter(s), but 2 were given; write `toLeaf` on its own for any instantiation
-/
#guard_msgs in
temporal (only := check) [tooManyArguments] 𝒲ℱ (toLeaf 1 2)

-- The proof reads an action as the model checker does
/--
error: action `toLeaf` takes 1 parameter(s), but 2 were given; write `toLeaf` on its own for any instantiation
-/
#guard_msgs in
temporal (only := verify) [tooManyArgumentsVerify] 𝒲ℱ (toLeaf 1 2)

/-- error: expected an action of this module, applied to arguments or not; the module's actions are [toLeaf, toHub, stay] -/
#guard_msgs in
temporal (only := check) [notAnAction] 𝒲ℱ (fun s s' => s ≠ s')

-- Without `(only := …)`, a fairness condition gets both definitions
#guard_msgs in
temporal [strongBoth] 𝒮ℱ (toLeaf 1) ∧ 𝒲ℱ toHub → ◇ ⌜ loc = (1 : Loc) ⌝

-- An action that is not applied stands for some instantiation of it on both sides: for the model checker
-- some label of it, and for the proof the union of its instantiations
#guard_msgs in
temporal [strongWholeBoth] 𝒮ℱ toLeaf ∧ 𝒲ℱ toHub → ◇ ⌜ loc = (1 : Loc) ⌝
-- Also in parentheses
#guard_msgs in
temporal [strongWholeParens] 𝒮ℱ (toLeaf) ∧ 𝒲ℱ toHub → ◇ ⌜ loc = (1 : Loc) ⌝
example : @strongWholeParens = @strongWholeBoth := rfl
temporal [someLeafEnabled] Enabled toLeaf ↔ ∃ l : Loc, Enabled (toLeaf l)

/-- info: ✅ No liveness violation (checked 1 properties, explored 1 product states) -/
#guard_msgs in
#temporal_check [someLeafEnabled] interpreted {}

prove_temporal_by [someLeafEnabled]
  tclear hInit hNext hInv
  tfinite_window
  simp only [Lentil.enabled]
  exact exists_comm

end TemporalFairness
