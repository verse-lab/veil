module

public import Veil

namespace InstantiateVisibility

class Marked (t : Type) where
  marked : t → Bool

public class Labelled (t : Type) where
  label : t → Nat

end InstantiateVisibility

open InstantiateVisibility

veil module InstantiatePrivateClass
type proc

/-- error: Class `Marked` must be public to be used with `instantiate`. Declare it with `public class`. -/
#guard_msgs in
instantiate m : Marked proc

private class Labelled (t : Type) where
  flag : t → Bool

/--
error: `Labelled` resolves to the private class `InstantiatePrivateClass.Labelled` here. Veil uses the public scope for generated declarations.

Hint: Qualify the intended public class in `instantiate`.
  [apply] InstantiateVisibility.Labelled
-/
#guard_msgs in
instantiate labels : Labelled proc

-- Recovery keeps the public instance available to the action below.
individual x : Nat
#gen_state
after_init { x := 0 }
action step (p : proc) { x := labels.label p }
invariant [nonneg] x ≥ 0
#gen_spec
end InstantiatePrivateClass

veil module InstantiateQualifiedShadow
private class InstantiateVisibility.Labelled (t : Type) where
  flag : t → Bool
type proc

/--
error: `InstantiateVisibility.Labelled` resolves to the private class `InstantiateQualifiedShadow.InstantiateVisibility.Labelled` here. Veil uses the public scope for generated declarations.

Hint: Qualify the intended public class in `instantiate`.
  [apply] _root_.InstantiateVisibility.Labelled
-/
#guard_msgs in
instantiate labels : (@InstantiateVisibility.Labelled proc)
end InstantiateQualifiedShadow
