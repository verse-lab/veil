import Veil.Frontend.DSL.Action.Semantics.Definitions
import Veil.Util.Meta
import Veil.Frontend.DSL.State.Types

/-! # Utilities for Displaying -/

namespace Veil

deriving instance Repr for DivM

instance [Repr κ] [Repr α] : Repr (PeDivM κ α) :=
  inferInstanceAs (Repr (_ × _))

instance : Repr Std.Format where
  reprPrec x _ := x

-- NOTE: Not sure why resolution does not work without this
instance [inst : Repr (m (Except ε α))] : Repr (ExceptT ε m α) := inst

instance (priority := high) finFunctionReprCurry (α₁ : Type u) (α₂ : Type v) (β : Type w)
  [Repr α₁] [FinEnum α₁] [Repr α₂] [FinEnum α₂] [Repr β] [inst : Repr (α₁ × α₂ → β)] :
  Repr (α₁ → α₂ → β) where
  reprPrec := fun f n => inst.reprPrec (fun (x, y) => f x y) n

instance (priority := low) finFunctionRepr (α : Type u) (β : Type v) [Repr α] [FinEnum α] [Repr β] :
  Repr (α → β) where
  reprPrec := fun f n =>
    let l := FinEnum.toList α
    let args := l.map (reprPrec · n)
    let res := l.map ((fun x => reprPrec x n) ∘ f)
    args.zip res |>.foldl
      (fun acc (a, b) => acc.append (a ++ " => " ++ b ++ Std.Format.line))
      ("finite_fun : ".toFormat)

instance (priority := high) essentiallyFinSetRepr (α : Type u) [Repr α] [FinEnum α] : Repr (α → Bool) where
  reprPrec := fun f => List.repr (FinEnum.toList α |>.filter f)

def reprFiniteFunc {α β} [FinEnum α] [Repr α] [Repr β] (f : α → β) : String :=
  (FinEnum.toList α).map (fun a => s!"{reprStr a}{reprStr (f a)}")
  |> String.intercalate ""

end Veil
