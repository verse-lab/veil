module

public import Veil.Frontend.DSL.State.Types
public meta import Veil.Frontend.DSL.State.Types

/-! Tests for deforested finite encoding and field type elaboration. -/

open Veil

namespace VeilTest.Deriving.FinEncodableInjOnly

private def checkEncodings [inst : FinEncodableInjOnly α] (values : List α) : IO Unit := do
  let encodings := values.map (inst.encode · |>.val)
  assert! encodings.eraseDups.length == values.length
  assert! encodings.all (· < inst.card)

-- Nullary constructors and the single-constructor proxy cases.
inductive Color where
  | red | green | blue
deriving FinEncodableInjOnly

#guard FinEncodableInjOnly.card (κ := Color) == 3
#guard (FinEncodableInjOnly.encode Color.red).val == 0
#guard (FinEncodableInjOnly.encode Color.green).val == 1
#guard (FinEncodableInjOnly.encode Color.blue).val == 2

inductive Singleton where
  | only
deriving FinEncodableInjOnly

#guard FinEncodableInjOnly.card (κ := Singleton) == 1
#guard (FinEncodableInjOnly.encode Singleton.only).val == 0

inductive Wrapper (α : Type u) where
  | wrap (value : α)
deriving FinEncodableInjOnly

#guard FinEncodableInjOnly.card (κ := Wrapper (Fin 5)) == 5
#guard (FinEncodableInjOnly.encode (Wrapper.wrap (3 : Fin 5))).val == 3

-- One parameter, mixed arities, and deeply nested Sigma encoding.
inductive Action (node : Type u) where
  | send (a b c d : node)
  | recv (x : node)
  | timeout
deriving FinEncodableInjOnly

example [FinEncodableInjOnly α] : FinEncodableInjOnly (Action α) := inferInstance

#guard FinEncodableInjOnly.card (κ := Action (Fin 2)) == 19
#guard (FinEncodableInjOnly.encode (Action.send (0 : Fin 2) 0 0 0)).val == 0
#guard (FinEncodableInjOnly.encode (Action.send (1 : Fin 2) 0 1 0)).val == 10
#guard (FinEncodableInjOnly.encode (Action.send (1 : Fin 2) 1 1 1)).val == 15
#guard (FinEncodableInjOnly.encode (Action.recv (0 : Fin 2))).val == 16
#guard (FinEncodableInjOnly.encode (Action.recv (1 : Fin 2))).val == 17
#guard (FinEncodableInjOnly.encode (Action.timeout (node := Fin 2))).val == 18

#eval do
  let nodes := List.finRange 2
  let sends := nodes.flatMap fun a => nodes.flatMap fun b =>
    nodes.flatMap fun c => nodes.map (Action.send a b c)
  checkEncodings (sends ++ nodes.map Action.recv ++ [Action.timeout])

-- Literal field types and cumulative constructor offsets.
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
  checkEncodings (values ++ [FunctionField.stop])

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
  | left (a : α)
  | right (b : β)
  | item (α : Hidden (α := α) n) (b : β)
  | stop
deriving FinEncodableInjOnly

example {α : Type u} {β : Type v} [FinEncodableInjOnly α] [FinEncodableInjOnly β]
    (n : Nat) : FinEncodableInjOnly (Generic α β n) := inferInstance

#guard FinEncodableInjOnly.card (κ := Generic (Fin 2) (Fin 3) 2) == 18
#guard (FinEncodableInjOnly.encode (Generic.left (β := Fin 3) (n := 2) (1 : Fin 2))).val == 1
#guard (FinEncodableInjOnly.encode (Generic.right (α := Fin 2) (n := 2) (2 : Fin 3))).val == 4
#guard (FinEncodableInjOnly.encode (Generic.item (Hidden.item (α := Fin 2) (n := 2) 1 1)
  (2 : Fin 3))).val == 16
#guard (FinEncodableInjOnly.encode (Generic.stop (α := Fin 2) (β := Fin 3) (n := 2))).val == 17

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
  checkEncodings values

-- Wide inductives, as `#gen_spec` derives for the action labels of a module with many
-- actions. The deforested encoding's equations are checked by the kernel (`veil_kernel_rfl`):
-- the elaborator's `rfl` unfolded `card` about 2^K times for K one-field constructors and ran
-- out of heartbeats at 24.
inductive Wide (node : Type u) where
  | a0 (n : node)
  | a1 (n : node)
  | a2 (n : node)
  | a3 (n : node)
  | a4 (n : node)
  | a5 (n : node)
  | a6 (n : node)
  | a7 (n : node)
  | a8 (n : node)
  | a9 (n : node)
  | a10 (n : node)
  | a11 (n : node)
  | a12 (n : node)
  | a13 (n : node)
  | a14 (n : node)
  | a15 (n : node)
  | a16 (n : node)
  | a17 (n : node)
  | a18 (n : node)
  | a19 (n : node)
  | a20 (n : node)
  | a21 (n : node)
  | a22 (n : node)
  | a23 (n : node)
deriving FinEncodableInjOnly

#guard FinEncodableInjOnly.card (κ := Wide (Fin 2)) == 48
#guard (FinEncodableInjOnly.encode (Wide.a0 (1 : Fin 2))).val == 1
#guard (FinEncodableInjOnly.encode (Wide.a12 (0 : Fin 2))).val == 24
#guard (FinEncodableInjOnly.encode (Wide.a23 (1 : Fin 2))).val == 47

example (x : Wide (Fin 3)) :
    FinEncodableInjOnly.encode x =
      (FinEncodableInjOnly.ofEquiv (veil_proxy_equiv% (Wide (Fin 3))).symm).encode x := by
  cases x <;> veil_kernel_rfl

-- Mixed field shapes, nullary constructors included.
inductive WideMixed (node : Type u) where
  | b0 (n : node)
  | b1 (m n : node)
  | b2 (n : node) (b : Bool)
  | b3 (b : Bool)
  | b4 (n : node)
  | b5
  | b6 (n : node) (b : Bool)
  | b7 (b : Bool)
  | b8 (n : node)
  | b9 (m n : node)
  | b10 (n : node) (b : Bool)
  | b11
  | b12 (n : node)
  | b13 (m n : node)
  | b14 (n : node) (b : Bool)
  | b15 (b : Bool)
  | b16 (n : node)
  | b17
  | b18 (n : node) (b : Bool)
  | b19 (b : Bool)
  | b20 (n : node)
  | b21 (m n : node)
  | b22 (n : node) (b : Bool)
  | b23
deriving FinEncodableInjOnly

example (x : WideMixed (Fin 2)) :
    FinEncodableInjOnly.encode x =
      (FinEncodableInjOnly.ofEquiv (veil_proxy_equiv% (WideMixed (Fin 2))).symm).encode x := by
  cases x <;> veil_kernel_rfl

/--
error: veil_kernel_rfl: the two sides are not definitionally equal
  ↑(FinEncodableInjOnly.encode (Wide.a1 0))
and
  0
-/
#guard_msgs in
example : (FinEncodableInjOnly.encode (Wide.a1 (0 : Fin 2))).val = 0 := by
  veil_kernel_rfl

end VeilTest.Deriving.FinEncodableInjOnly
