module

public import Veil

/-! Quantifiers in a model-checked property: `∀ x, φ` and `∃ x, φ` are the conjunction and the disjunction
of `φ` over the values that `Enumeration` lists for the type of `x`. -/

veil module TemporalQuantifiersHub

abbrev Loc := Fin 3
individual loc : Loc

after_init { loc := (0 : Loc) }

-- From the hub `0` one steps to a leaf, where one can stay or step back
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

-- HOLDS: strong fairness of every `toLeaf l` visits every location infinitely often
temporal (only := check) [allVisited] (∀ l : Loc, SF(toLeaf l)) ∧ WF(toHub) → ∀ l : Loc, □ ◇ ⌜ loc = l ⌝
temporal (only := check) [allVisitedByHand]
  ((SF(toLeaf 0) ∧ SF(toLeaf 1) ∧ SF(toLeaf 2)) ∧ WF(toHub)) →
    (□ ◇ ⌜ loc = 0 ⌝) ∧ (□ ◇ ⌜ loc = 1 ⌝) ∧ (□ ◇ ⌜ loc = 2 ⌝)
-- The same, with the type of `l` inferred from `toLeaf l`
temporal (only := check) [allVisitedInferred] (∀ l, SF(toLeaf l)) ∧ WF(toHub) → ∀ l : Loc, □ ◇ ⌜ loc = l ⌝
-- FAILS: strong fairness of `toLeaf` as a whole is met by the run `0, 2, 0, 2, …`
temporal (only := check) [wholeFails] SF(toLeaf) ∧ WF(toHub) → ∀ l : Loc, □ ◇ ⌜ loc = l ⌝
-- HOLDS: every run reaches some leaf
temporal (only := check) [someLeaf] ∃ l : Loc, ◇ ⌜ loc = l ∧ l ≠ 0 ⌝
temporal (only := check) [someLeafByHand]
  (◇ ⌜ loc = 0 ∧ (0 : Loc) ≠ 0 ⌝) ∨ (◇ ⌜ loc = 1 ∧ (1 : Loc) ≠ 0 ⌝) ∨ (◇ ⌜ loc = 2 ∧ (2 : Loc) ≠ 0 ⌝)
-- FAILS: the run `0, 1, 1, …` never reaches leaf 2
temporal (only := check) [everyLeafFails] ∀ l : Loc, ◇ ⌜ loc = l ⌝

#gen_spec

-- Instantiated, the quantifiers give the formulas written out
#guard (allVisited.ast Theory (State FieldConcreteType) FieldConcreteType).φ ==
  (allVisitedByHand.ast Theory (State FieldConcreteType) FieldConcreteType).φ
#guard (allVisitedInferred.ast Theory (State FieldConcreteType) FieldConcreteType).φ ==
  (allVisitedByHand.ast Theory (State FieldConcreteType) FieldConcreteType).φ
#guard (someLeaf.ast Theory (State FieldConcreteType) FieldConcreteType).φ ==
  (someLeafByHand.ast Theory (State FieldConcreteType) FieldConcreteType).φ

/-- info: ✅ No liveness violation (checked 1 properties, explored 16 product states) -/
#guard_msgs in
#liveness_check [allVisited] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 16 product states) -/
#guard_msgs in
#liveness_check [allVisitedByHand] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 16 product states) -/
#guard_msgs in
#liveness_check [allVisitedInferred] interpreted {}
/-- error: ❌ Violation: liveness_failure (violates: wholeFails) -/
#guard_msgs (substring := true) in
#liveness_check [wholeFails] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 3 product states) -/
#guard_msgs in
#liveness_check [someLeaf] interpreted {}
/-- info: ✅ No liveness violation (checked 1 properties, explored 3 product states) -/
#guard_msgs in
#liveness_check [someLeafByHand] interpreted {}
/-- error: ❌ Violation: liveness_failure (violates: everyLeafFails) -/
#guard_msgs (substring := true) in
#liveness_check [everyLeafFails] interpreted {}

-- Binder predicates are not supported
/--
error: a model-checked property can only use the atoms `⌜ … ⌝`, `⌞ … ⌟`, `E(…)` and `T(…)`, the fairness conditions `WF(…)` and `SF(…)`, the connectives `⊤`, `⊥`, `¬`, `∧`, `∨`, `→`, `↔`, `□`, `◇`, `◯`, `𝑈`, `↝` and `⇒`, and the quantifiers `∀ x, …`, `∀ x : T, …`, `∃ x, …` and `∃ x : T, …`; this formula is none of them
-/
#guard_msgs in
temporal (only := check) [bounded] ∀ l > (0 : Loc), ◇ ⌜ loc = l ⌝

end TemporalQuantifiersHub

veil module TemporalQuantifiersSorts

type node
individual atHub : Bool
relation visiting : node → Bool

after_init { atHub := true; visiting N := false }

-- From the hub one visits a node and comes back
action go (n : node) {
  require atHub
  atHub := false
  visiting n := true
}
action back {
  require ¬ atHub
  atHub := true
  visiting N := false
}

ghost relation isVisited (n : node) := visiting n

-- HOLDS: strong fairness of every `go n` visits every node
temporal (only := check) [eachVisited] (∀ n, SF(go n)) ∧ WF(back) → ∀ n, □ ◇ ⌜ visiting n ⌝
-- FAILS: strong fairness of `go` as a whole is met by always visiting the same node
temporal (only := check) [eachVisitedWhole] SF(go) ∧ WF(back) → ∀ n, □ ◇ ⌜ visiting n ⌝
-- HOLDS: nested quantifiers, and a ghost under them
temporal (only := check) [nested] (∀ n, SF(go n)) ∧ WF(back) → ∀ n, ∃ m, □ ◇ ⌜ isVisited m ∧ m = n ⌝
-- HOLDS: the `Decidable` instance of the atom depends on `n`
temporal (only := check) [atMostOne] □ ∀ n, ⌜ visiting n → ∀ m, visiting m → m = n ⌝
-- HOLDS, and also gets its proof definition, through Lentil's `∃`
temporal [someVisited] ∃ n, ◇ ⌜ visiting n ⌝
-- No temporal quantifier
temporal (only := check) [anyVisited] ◇ ⌜ ∃ n, visiting n ⌝

-- Nothing is dropped
#guard_msgs in
#gen_spec

-- Only the model-checking definitions with a temporal quantifier take an `Enumeration` instance
open Lean in
run_meta do
  let takesEnumeration (n : Name) : MetaM Bool :=
    return (← getConstInfo n).type.getUsedConstants.contains ``Veil.Enumeration
  for n in [``TemporalQuantifiersSorts.eachVisited.ast, ``TemporalQuantifiersSorts.nested.ast,
      ``TemporalQuantifiersSorts.atMostOne.ast, ``TemporalQuantifiersSorts.someVisited.ast] do
    unless ← takesEnumeration n do throwError "{n} does not take an `Enumeration` instance"
  for n in [``TemporalQuantifiersSorts.anyVisited.ast, ``TemporalQuantifiersSorts.someVisited] do
    if ← takesEnumeration n then throwError "{n} takes an `Enumeration` instance"

/-- info: ✅ No liveness violation (checked 5 properties, explored 35 product states) -/
#guard_msgs in
#liveness_check [eachVisited] [nested] [atMostOne] [someVisited] [anyVisited] interpreted { node := Fin 2 }
/-- info: ✅ No liveness violation (checked 5 properties, explored 62 product states) -/
#guard_msgs in
#liveness_check [eachVisited] [nested] [atMostOne] [someVisited] [anyVisited] interpreted { node := Fin 3 }
/-- error: ❌ Violation: liveness_failure (violates: eachVisitedWhole) -/
#guard_msgs (substring := true) in
#liveness_check [eachVisitedWhole] interpreted { node := Fin 2 }

-- Without an `Enumeration Nat` instance, `#liveness_check` cannot instantiate the property
temporal (only := check) [overNat] ∀ k : Nat, ◇ ⌜ k = k ⌝

/--
error: failed to synthesize instance of type class
  Enumeration Nat
-/
#guard_msgs (substring := true) in
#liveness_check [overNat] interpreted { node := Fin 2 }

end TemporalQuantifiersSorts
