module

public import Veil

/-! Regression tests for A03: field types must retain their elaborated expressions. -/

open Veil

namespace VeilTest.Deriving.FinEncodableInjOnly

inductive Literal where
  | item (x : Fin 3)
  | pair (x : Fin 2) (y : Fin 3)
  | stop
deriving FinEncodableInjOnly

#guard FinEncodableInjOnly.card (κ := Literal) == 10
#guard (FinEncodableInjOnly.encode (Literal.item 2)).val == 2
#guard (FinEncodableInjOnly.encode (Literal.pair 1 2)).val == 8
#guard (FinEncodableInjOnly.encode Literal.stop).val == 9

abbrev Three := Fin 3
abbrev Pred := Fin 2 → Bool

inductive FunctionField where
  | item (f : Fin 2 → Bool) (x : Fin 3)
  | stop
deriving FinEncodableInjOnly

inductive AliasedFunctionField where
  | item (f : Pred) (x : Three)
  | stop
deriving FinEncodableInjOnly

#guard FinEncodableInjOnly.card (κ := FunctionField) == 13
#guard (FinEncodableInjOnly.encode FunctionField.stop).val == 12

example (f : Pred) (x : Three) :
    (FinEncodableInjOnly.encode (FunctionField.item f x)).val =
      (FinEncodableInjOnly.encode (AliasedFunctionField.item f x)).val := rfl

-- Check all four functions and all three indices, including the final offset.
#eval do
  let functions : List Pred := [fun _ => false, fun _ => true,
    fun i => i.val == 0, fun i => i.val == 1]
  let values := functions.flatMap fun f => [0, 1, 2].map (FunctionField.item f)
  let encodings := (values ++ [FunctionField.stop]).map (FinEncodableInjOnly.encode · |>.val)
  assert! encodings.eraseDups.length == 13
  assert! encodings.all (· < 13)

-- Literal, lambda, let, and dependent function binders inside field types.
inductive Compound where
  | subtype (x : { i : Fin 3 // i.val < 2 })
  | localLet (x : let n := 3; Fin n)
  | dependentFunction (f : (i : Fin 2) → Fin (i.val + 1))
  | stop
deriving FinEncodableInjOnly

#guard FinEncodableInjOnly.card (κ := Compound) == 8
#guard (FinEncodableInjOnly.encode Compound.stop).val == 7

-- Direct arithmetic must still be definitionally equal to the proxy encoding.
example (x : Literal) :
    FinEncodableInjOnly.encode x =
      (FinEncodableInjOnly.ofEquiv (veil_proxy_equiv% Literal).symm).encode x := by
  cases x <;> rfl

example (x : FunctionField) :
    FinEncodableInjOnly.encode x =
      (FinEncodableInjOnly.ofEquiv (veil_proxy_equiv% FunctionField).symm).encode x := by
  cases x <;> rfl

example (x : Compound) :
    FinEncodableInjOnly.encode x =
      (FinEncodableInjOnly.ofEquiv (veil_proxy_equiv% Compound).symm).encode x := by
  cases x <;> rfl

-- Parameter references, implicit type arguments, and distinct universes survive
-- embedding. The field binder deliberately shadows the type parameter's name.
inductive Hidden {α : Type u} (n : Nat) where
  | item (x : α) (i : Fin n)
deriving FinEncodableInjOnly

inductive Generic (α : Type u) (β : Type v) (n : Nat) where
  | item (α : Hidden (α := α) n) (b : β)
  | stop
deriving FinEncodableInjOnly

example {α : Type u} {β : Type v} [FinEncodableInjOnly α] [FinEncodableInjOnly β]
    (n : Nat) : FinEncodableInjOnly (Generic α β n) := inferInstance

#guard FinEncodableInjOnly.card (κ := Generic (Fin 2) (Fin 3) 2) == 13
#guard (FinEncodableInjOnly.encode (Generic.item (Hidden.item (α := Fin 2) (n := 2) 1 1)
  (2 : Fin 3))).val == 11
#guard (FinEncodableInjOnly.encode (Generic.stop (α := Fin 2) (β := Fin 3) (n := 2))).val == 12

-- A parameter occurring under a function binder must refer to this instance's n.
inductive ParameterFunction (n : Nat) where
  | item (f : Fin n → Bool)
  | stop
deriving FinEncodableInjOnly

example (n : Nat) : FinEncodableInjOnly (ParameterFunction n) := inferInstance

#guard FinEncodableInjOnly.card (κ := ParameterFunction 2) == 5
#guard (FinEncodableInjOnly.encode (ParameterFunction.stop (n := 2))).val == 4

-- Implicit constructor fields must be bound in the generated match arm too.
inductive ImplicitField where
  | item {i : Fin 3} (b : Bool)
  | stop
deriving FinEncodableInjOnly

#guard FinEncodableInjOnly.card (κ := ImplicitField) == 7
#guard (FinEncodableInjOnly.encode ImplicitField.stop).val == 6

-- Dependent constructor fields require the generic Sigma encoding: their
-- cardinality cannot be computed by multiplying independent field cards.
inductive DependentFields where
  | item (n : Fin 3) (i : Fin (n.val + 1))
  | stop
deriving FinEncodableInjOnly

#guard FinEncodableInjOnly.card (κ := DependentFields) == 7
#guard (FinEncodableInjOnly.encode DependentFields.stop).val == 6

#eval do
  let values : List DependentFields :=
    [.item 0 0, .item 1 0, .item 1 1, .item 2 0, .item 2 1, .item 2 2, .stop]
  let encodings := values.map (FinEncodableInjOnly.encode · |>.val)
  assert! encodings.eraseDups.length == 7
  assert! encodings.all (· < 7)

end VeilTest.Deriving.FinEncodableInjOnly
