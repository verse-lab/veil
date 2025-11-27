import Veil.Core.Tools.Checker.Concrete.State
import Veil.Core.Tools.Checker.Concrete.DataStructure
import Veil.Core.Tools.Checker.Concrete.Util
import Veil.Core.Tools.Checker.Concrete.Concretize
import Veil.Core.Tools.Checker.Concrete.Runlib


def reprFiniteFunc {α β} [FinEnum α] [Repr α] [Repr β] (f : α → β) : String :=
  (FinEnum.toList α).map (fun a => s!"{reprStr a}{reprStr (f a)}")
  |> String.intercalate ""

instance (priority := high) finFunctionReprCurry (α₁ : Type u) (α₂ : Type v) (β : Type w)
  [Repr α₁] [FinEnum α₁] [Repr α₂] [FinEnum α₂] [Repr β] [inst : Repr (α₁ × α₂ → β)] :
  Repr (α₁ → α₂ → β) where
  reprPrec := fun f n => inst.reprPrec (fun (x, y) => f x y) n

open Lean in
instance (priority := low) finFunctionRepr (α : Type u) (β : Type v) [Repr α] [FinEnum α] [Repr β] :
  Repr (α → β) where
  reprPrec := fun f n =>
    let l := FinEnum.toList α
    let args := l.map (reprPrec · n)
    let res := l.map ((fun x => reprPrec x n) ∘ f)
    args.zip res |>.foldl
      (fun acc (a, b) => acc.append (a ++ " => " ++ b ++ Format.line))
      ("finite_fun : ".toFormat)

instance (priority := high) essentiallyFinSetRepr (α : Type u) [Repr α] [FinEnum α] : Repr (α → Bool) where
  reprPrec := fun f => List.repr (FinEnum.toList α |>.filter f)
