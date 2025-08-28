import Lean

namespace Veil

/-- Attribute added to `Wp` constructs, to unfold them. -/
register_simp_attr wpSimp

/-- Implementation detail. Tagged to `act.do` and constructs that
should be unfolded when elaborating action's definitions. -/
register_simp_attr doSimp

/-- Attribute added to `StateAssertion`s, to unfold them. -/
register_simp_attr invSimp

end Veil
