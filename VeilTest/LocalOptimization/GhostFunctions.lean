module

public import Veil

set_option linter.unusedVariables false

veil module LocalGhostFunctions

type node
relation r : node → node → Bool
function rank : node → Nat
immutable function baseRank : node → Nat
immutable relation edge : node → node → Bool

#gen_state

-- Value-returning definitions must get locality proofs of their own, including
-- inferred and function-valued return types and nested theory/state calls.
#guard_msgs in
theory ghost function base (n : node) : Nat := baseRank n
#guard_msgs in
theory ghost function baseTwice (n : node) := base n + base n
#guard_msgs in
theory ghost function baseFn : node → Nat := fun n => base n
#guard_msgs in
ghost function getRank (n : node) : Nat := rank n
#guard_msgs in
ghost function total (n : node) := getRank n + baseTwice n
#guard_msgs in
ghost function rankFn : node → Nat := fun n => getRank n
#guard_msgs in
ghost function resultType : Type := Nat

-- The generated Decidable parameters mention concrete fields. Locality must
-- bridge them to abstract fields with proofs, also when the result is data.
#guard_msgs in
theory ghost function theoryChoice (n : node) : Nat :=
  if ∀ m, edge n m then base n else 0
#guard_msgs in
ghost function stateChoice (n : node) : Nat :=
  if ∀ m, r n m then total n else theoryChoice n
#guard_msgs in
ghost relation nestedValid := ∀ n, stateChoice n ≤ total n + theoryChoice n

-- Existentials and alternating quantifiers need extracted instances too. The
-- conditions depend on several concrete fields, and the branches call other
-- ghost functions that carry their own Decidable parameters.
#guard_msgs in
theory ghost function theoryExistsChoice (n : node) : Nat :=
  if ∃ m, edge n m ∧ baseRank m ≤ baseRank n then base n else 0
#guard_msgs in
theory ghost function theoryAlternatingChoice (n : node) : Nat :=
  if ∀ m, ∃ k, edge n k ∧ edge k m then theoryExistsChoice n else baseTwice n
#guard_msgs in
ghost function stateExistsChoice (n : node) : Nat :=
  if ∃ m, r n m ∧ rank m ≤ rank n then getRank n else theoryExistsChoice n

-- Exercise Decidable through `decide` as well as `if`, returning actual Bool
-- data under alternating quantifiers rather than a proposition.
#guard_msgs in
ghost function quantifiedBool (n : node) : Bool :=
  decide (∃ m, r n m ∧ ∀ k, r m k → rank k ≤ rank n)

-- Capitalization must not merge distinct declaration names.
#guard_msgs in
theory ghost relation TheoryValid := ∀ n, base n = base n
#guard_msgs in
assumption [theoryValid] TheoryValid
#guard_msgs in
ghost relation Valid := nestedValid
#guard_msgs in
invariant [valid] Valid

after_init {
  r N M := false
  rank N := 0
}
action idle { require True }
#guard_msgs in
#gen_spec

-- These are the cross-representation theorems, not just fixed-environment
-- instances; their construction compares the two separately obtained cores.
run_cmd do
  let quantifiedFunctions := [``theoryExistsChoice, ``theoryAlternatingChoice,
    ``stateExistsChoice, ``quantifiedBool]
  for name in quantifiedFunctions do
    let info ← Lean.getConstInfo name
    unless info.type.getUsedConstantsAsSet.contains ``Decidable do
      throwError "{name} should carry an extracted Decidable parameter"
  for name in [``base, ``baseTwice, ``baseFn, ``getRank, ``total, ``rankFn, ``resultType,
      ``theoryChoice, ``stateChoice, ``nestedValid, ``Valid, ``valid, ``TheoryValid, ``theoryValid]
      ++ quantifiedFunctions do
    discard <| Lean.getConstInfo (name ++ `local_abstract_eq)
  discard <| Lean.getConstInfo ``Invariants.core_simplified_eq
  discard <| Lean.getConstInfo ``Assumptions.core_simplified_eq

end LocalGhostFunctions
