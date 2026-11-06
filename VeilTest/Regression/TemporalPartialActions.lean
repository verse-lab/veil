module

public import Veil

/-! An action in `Enabled a`, `⟨ a ⟩`, `𝒲ℱ a` and `𝒮ℱ a` can be partially applied. A parameter left open,
as `·` or by leaving out the trailing arguments, stands for some value of it: for the model checker, the
label predicate leaves it unconstrained, and for the proof, it is existentially quantified. -/

veil module TemporalPartialActions

abbrev Loc := Fin 3
individual loc : Loc

after_init { loc := (0 : Loc) }

-- `hop src dst` moves from `src` to another location `dst`
action hop (src dst : Loc) {
  require loc = src ∧ src ≠ dst
  loc := dst
}
-- Never enabled, it gives the label predicates a constructor that is not `hop`
action halt {
  require False
}

-- HOLDS: an open parameter is the disjunction over its values, for the leading and the trailing ones
temporal (only := check) [enabledOpenFirst] □ (Enabled (hop · 1) ↔ ∃ s, Enabled (hop s 1))
temporal (only := check) [enabledOpenLast] □ (Enabled (hop 0) ↔ ∃ d, Enabled (hop 0 d))
temporal (only := check) [takenOpenFirst] □ (⟨ hop · 1 ⟩ ↔ ∃ s, ⟨ hop s 1 ⟩)
temporal (only := check) [takenOpenLast] □ (⟨ hop 0 · ⟩ ↔ ∃ d, ⟨ hop 0 d ⟩)
temporal (only := check) [takenAllOpen] □ (⟨ hop · · ⟩ ↔ ⟨ hop ⟩)
-- HOLDS: `Enabled` takes its action without parentheses, as `Enabled hop 0` does
temporal (only := check) [noParens] □ (Enabled hop · 1 ↔ Enabled (hop · 1))
-- FAILS, both: the steps into `1` are some steps but not all
temporal (only := check) [alwaysIntoOne] □ ⟨ hop · 1 ⟩
temporal (only := check) [neverIntoOne] □ ¬ ⟨ hop · 1 ⟩

-- Fairness of the steps into `1`, from anywhere, lies between that of one instantiation and that of `hop`
-- as a whole. HOLDS: a run that eventually stays out of `1` always has a step into `1` enabled.
temporal (only := check) [intoOneFair] 𝒲ℱ (hop · 1) → □ ◇ ⌜ loc = 1 ⌝
-- FAILS: the run `0, 2, 0, 2, …` is weakly fair to the steps out of `0`, which it disables at `2`
temporal (only := check) [outOfZeroFair] 𝒲ℱ (hop 0) → □ ◇ ⌜ loc = 1 ⌝
-- FAILS: the same run is weakly fair to `hop` as a whole
temporal (only := check) [wholeFair] 𝒲ℱ hop → □ ◇ ⌜ loc = 1 ⌝
-- HOLDS. The quantified variable has the name of the parameter, which the label predicate must not capture.
temporal [allIntoFair] (∀ dst, 𝒲ℱ (hop · dst)) → ∀ dst, □ ◇ ⌜ loc = dst ⌝

#gen_spec

/-- info: ✅ No liveness violation (checked 6 properties, explored 18 product states) -/
#guard_msgs in
#temporal_check [enabledOpenFirst] [enabledOpenLast] [takenOpenFirst] [takenOpenLast] [takenAllOpen] [noParens]
  interpreted {}
/-- error: ❌ Violation: liveness_failure (violates: alwaysIntoOne) -/
#guard_msgs (substring := true) in
#temporal_check [alwaysIntoOne] interpreted {}
/-- error: ❌ Violation: liveness_failure (violates: neverIntoOne) -/
#guard_msgs (substring := true) in
#temporal_check [neverIntoOne] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 6 product states) -/
#guard_msgs in
#temporal_check [intoOneFair] interpreted {}
/-- error: ❌ Violation: liveness_failure (violates: outOfZeroFair) -/
#guard_msgs (substring := true) in
#temporal_check [outOfZeroFair] interpreted {}
/-- error: ❌ Violation: liveness_failure (violates: wholeFair) -/
#guard_msgs (substring := true) in
#temporal_check [wholeFair] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 12 product states) -/
#guard_msgs in
#temporal_check [allIntoFair] interpreted {}

-- Leaving out the trailing arguments is the same as writing `·` for them, on both sides
temporal [fairOmitted] 𝒲ℱ (hop 0)
temporal [fairDotted] 𝒲ℱ (hop 0 ·)
temporal [fairAllDotted] 𝒮ℱ (hop · ·)
temporal [fairUnapplied] 𝒮ℱ hop
example : @fairOmitted = @fairDotted := rfl
example : @fairAllDotted = @fairUnapplied := rfl
-- `p.ast` also holds the name of `p`, so only the formulas are compared
open Lean in
run_meta do
  let formulaOf (n : Name) : MetaM Expr := do
    let some e := (← getConstInfo n).value!.find? (·.isAppOf ``Veil.LivenessMC.LivenessProperty.ofFormula)
      | throwError "{n} is not built by `LivenessProperty.ofFormula`"
    return e.appArg!
  for (a, b) in [(``fairOmitted.ast, ``fairDotted.ast), (``fairAllDotted.ast, ``fairUnapplied.ast)] do
    unless (← formulaOf a) == (← formulaOf b) do
      throwError "{a} and {b} have different formulas"

-- The proof reads an open parameter as an existential, which commutes with `Enabled` and `⟨ … ⟩`
temporal [enabledOpenFirstProved] Enabled (hop · 1) ↔ ∃ s, Enabled (hop s 1)
temporal [takenOpenLastProved] ⟨ hop 0 · ⟩ ↔ ∃ d, ⟨ hop 0 d ⟩

prove_temporal_by [enabledOpenFirstProved]
  tclear hInit hNext hInv
  tfinite_window
  simp only [Lentil.enabled]
  exact exists_comm

prove_temporal_by [takenOpenLastProved]
  tclear hInit hNext hInv
  tfinite_window
  exact Iff.rfl

/--
error: action `hop` takes 2 parameter(s), but 3 were given; write `·` for a parameter that can take any value
-/
#guard_msgs in
temporal (only := check) [tooManyArguments] 𝒲ℱ (hop 0 1 2)

/--
error: action `hop` takes 2 parameter(s), but 3 were given; write `·` for a parameter that can take any value
-/
#guard_msgs in
temporal (only := verify) [tooManyArgumentsVerify] 𝒲ℱ (hop · 1 2)

end TemporalPartialActions

/-! Over a sort, the open parameters of a label are left unconstrained, and the given ones compared through the
sort's `DecidableEq`. -/

veil module TemporalPartialActionsSorts

type node
relation pending : node → node → Bool
relation received : node → Bool

after_init {
  pending S D := false
  received N := false
}

action send (src dst : node) {
  pending src dst := true
}
action deliver (src dst : node) {
  require pending src dst
  pending src dst := false
  received dst := true
}

-- HOLDS
temporal (only := check) [enabledOpen] ∀ dst, □ (Enabled (deliver · dst) ↔ ∃ s, Enabled (deliver s dst))
temporal (only := check) [takenOpen] ∀ dst, □ (⟨ deliver · dst ⟩ ↔ ∃ s, ⟨ deliver s dst ⟩)
-- HOLDS: once `dst` has a pending message and nothing is delivered to it, a delivery to it stays enabled
temporal [allReceived]
  (∀ dst, 𝒲ℱ (deliver · dst)) → ∀ src, ∀ dst, □ (⌜ pending src dst ⌝ → ◇ ⌜ received dst ⌝)
-- FAILS: weak fairness of `deliver` as a whole is met by delivering to one destination only
temporal (only := check) [wholeReceived]
  𝒲ℱ deliver → ∀ src, ∀ dst, □ (⌜ pending src dst ⌝ → ◇ ⌜ received dst ⌝)

#gen_spec

/-- info: ✅ No liveness violation (checked 3 properties, explored 667 product states) -/
#guard_msgs in
#temporal_check [enabledOpen] [takenOpen] [allReceived] interpreted { node := Fin 2 }
/-- error: ❌ Violation: liveness_failure (violates: wholeReceived) -/
#guard_msgs (substring := true) in
#temporal_check [wholeReceived] interpreted { node := Fin 2 }

end TemporalPartialActionsSorts
