import Lean

namespace Veil

/-- Attribute added to `Wp` constructs, to unfold them. -/
register_simp_attr wpSimp

/-- Attribute added to `wp` equations of monadic constructs and actions/procedures. -/
register_simp_attr wpEqSimp

/-- Attribute added to `.wpgen` definitions of actions/procedures. -/
register_simp_attr wpDefUnfoldSimp

/-- Attribute added to definitions/theorems related to `IsSubStateOf` and `IsSubReaderOf`. -/
register_simp_attr substateSimp

/-- Implementation detail. Tagged to `act.do` and constructs that
should be unfolded when elaborating action's definitions. -/
register_simp_attr doSimp

/-- Attribute added to `StateAssertion`s, to unfold them. Despite what
the might suggest, this is also added to `safety`, `trusted invariant`,
and `assumption` assertions. -/
register_simp_attr invSimp

/-- Attribute added to `DerivedDefinition`s that are `.invariantLike`
or `.assumptionLike`, to unfold them. -/
register_simp_attr derivedInvSimp

/-- Attribute added to Veil actions, to unfold them. -/
register_simp_attr actSimp

/-- Attribute added to `DerivedDefinition`s that are `.actionLike`, to unfold them. -/
register_simp_attr derivedActSimp

/-- Attribute added to theorems about invariants. -/
register_simp_attr invProof

/-- Lemmas to perform simplification of `if` expressions, before `split_ifs` is
called. -/
register_simp_attr ifSimp

/-- To enable `assumption`s to be used as predicates. -/
instance funOneArgBoolToProp : Coe (α → Bool) (α → Prop) where
  coe f a := f a = true

/-- To enable `invariant`s to be used as predicates. -/
instance funTwoArgsBoolToProp : Coe (α → β → Bool) (α → β → Prop) where
  coe f a b := f a b = true

end Veil
