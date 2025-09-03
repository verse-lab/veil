import Lean

namespace Veil

/-- Attribute added to `Wp` constructs, to unfold them. -/
register_simp_attr wpSimp

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

/-- Attribute added to `DerivedDefinition`s that are `.actionLike`, to unfold them. -/
register_simp_attr derivedActSimp

end Veil
