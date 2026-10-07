module

public import Veil

/-! Regression tests for structure enumeration completeness and candidate order. -/

open Veil

namespace VeilTest.Deriving.Enumeration

-- Default simp rules expand Bool/Fin existentials; deriving must not depend on them.
structure BoolPair where
  x : Bool
  y : Bool
deriving DecidableEq, Enumeration

#guard Enumeration.allValues (α := BoolPair) ==
  [⟨false, false⟩, ⟨false, true⟩, ⟨true, false⟩, ⟨true, true⟩]

structure FinPair where
  x : Fin 2
  y : Fin 2
deriving DecidableEq, Enumeration

#guard Enumeration.allValues (α := FinPair) ==
  [⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]

structure Generic (α β : Type) where
  first : α
  middle : β
  last : α
deriving Enumeration

#guard (Enumeration.allValues (α := Generic Bool (Fin 2))).length == 8

structure WithFunction where
  predicate : Fin 2 → Bool
  tag : Bool
deriving Enumeration

#guard (Enumeration.allValues (α := WithFunction)).length == 8

structure NoFields where
deriving DecidableEq, Enumeration

#guard Enumeration.allValues (α := NoFields) == [⟨⟩]

-- A parameterized fieldless structure uses the structure handler rather than
-- the enum handler. Its unused parameter does not need an Enumeration instance.
structure Phantom (α : Type) where
deriving Enumeration

example {α : Type} (a : Phantom α) : a ∈ Enumeration.allValues :=
  Enumeration.complete a

#guard (Enumeration.allValues (α := Phantom Nat)).length == 1

structure NoValues where
  impossible : Fin 0
  tag : Bool
deriving Enumeration

#guard (Enumeration.allValues (α := NoValues)).isEmpty

structure Parent where
  flag : Bool
deriving Enumeration

structure Child extends Parent where
  index : Fin 2
deriving Enumeration

#guard (Enumeration.allValues (α := Child)).length == 4

inductive Repeated where
  | first | second
deriving DecidableEq

instance : Enumeration Repeated where
  allValues := [.first, .second, .first]
  complete a := by cases a <;> simp

structure WithRepeats where
  value : Repeated
  tag : Bool
deriving DecidableEq, Enumeration

#guard Enumeration.allValues (α := WithRepeats) ==
  [⟨.first, false⟩, ⟨.first, true⟩, ⟨.second, false⟩,
   ⟨.second, true⟩, ⟨.first, false⟩, ⟨.first, true⟩]

end VeilTest.Deriving.Enumeration
