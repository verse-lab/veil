module

public import Veil.Frontend.DSL.Action.Semantics.Definitions
public meta import Veil.Util.Meta
public import Veil.Frontend.DSL.State.Types
public import Veil.Util.ValueDisplay

public section

/-! # Utilities for Displaying -/

namespace Veil

instance [Repr κ] [Repr α] : Repr (PeDivM κ α) :=
  inferInstanceAs (Repr (_ × _))

instance : Repr Std.Format where
  reprPrec x _ := x

-- NOTE: Not sure why resolution does not work without this
instance {ε α : Type u} [inst : Repr (m (Except ε α))] : Repr (ExceptT ε m α) := inst

instance (priority := high) finFunctionReprCurry (α₁ : Type u) (α₂ : Type v) (β : Type w)
  [Repr α₁] [Enumeration α₁] [Repr α₂] [Enumeration α₂] [Repr β] [inst : Repr (α₁ × α₂ → β)] :
  Repr (α₁ → α₂ → β) where
  reprPrec := fun f n => inst.reprPrec (fun (x, y) => f x y) n

/-- Repr for finite functions: the map of all input/output pairs, as in `finFunctionToJson`. A
function of several arguments is uncurried by `finFunctionReprCurry`, so its keys are tuples. -/
instance (priority := low) finFunctionRepr (α : Type u) (β : Type v) [Repr α] [Enumeration α] [Repr β] :
  Repr (α → β) where
  reprPrec f _ := ValueDisplay.mapFormat ((Enumeration.allValues (α := α)).map fun a => (a, f a))

/-- Repr for boolean predicates: the set of the elements where the predicate is true, as in
`essentiallyFinSetToJson`. -/
instance (priority := high) essentiallyFinSetRepr (α : Type u) [Repr α] [Enumeration α] : Repr (α → Bool) where
  reprPrec f _ := ValueDisplay.setFormat ((Enumeration.allValues (α := α)).filter f)

end Veil
