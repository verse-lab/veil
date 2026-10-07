module

public import Veil

/-! Performance regressions for deriving Enumeration on wide structures.

Check completeness proofs for 32/64 Bool fields, 32 Fin fields and 32 mixed fields
under the default Lean options and simp rules. The large candidate lists are never
evaluated: this test measures compilation of the derived enumerators and proofs.
-/

set_option linter.unusedVariables false

namespace VeilTest.Performance.DerivingEnumeration

-- The original 32-Bool-field regression for the simp/grind-based proof generator.
structure A where
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  b7 : Bool
  b8 : Bool
  b9 : Bool
  b10 : Bool
  b11 : Bool
  b12 : Bool
  b13 : Bool
  b14 : Bool
  b15 : Bool
  b16 : Bool
  b17 : Bool
  b18 : Bool
  b19 : Bool
  b20 : Bool
  b21 : Bool
  b22 : Bool
  b23 : Bool
  b24 : Bool
  b25 : Bool
  b26 : Bool
  b27 : Bool
  b28 : Bool
  b29 : Bool
  b30 : Bool
  b31 : Bool
  b32 : Bool
deriving Veil.Enumeration

example (x : A) : x ∈ Veil.Enumeration.allValues :=
  Veil.Enumeration.complete x

-- Double the width of the original regression; the value space has 2^64 elements.
structure Bool64 where
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  b7 : Bool
  b8 : Bool
  b9 : Bool
  b10 : Bool
  b11 : Bool
  b12 : Bool
  b13 : Bool
  b14 : Bool
  b15 : Bool
  b16 : Bool
  b17 : Bool
  b18 : Bool
  b19 : Bool
  b20 : Bool
  b21 : Bool
  b22 : Bool
  b23 : Bool
  b24 : Bool
  b25 : Bool
  b26 : Bool
  b27 : Bool
  b28 : Bool
  b29 : Bool
  b30 : Bool
  b31 : Bool
  b32 : Bool
  b33 : Bool
  b34 : Bool
  b35 : Bool
  b36 : Bool
  b37 : Bool
  b38 : Bool
  b39 : Bool
  b40 : Bool
  b41 : Bool
  b42 : Bool
  b43 : Bool
  b44 : Bool
  b45 : Bool
  b46 : Bool
  b47 : Bool
  b48 : Bool
  b49 : Bool
  b50 : Bool
  b51 : Bool
  b52 : Bool
  b53 : Bool
  b54 : Bool
  b55 : Bool
  b56 : Bool
  b57 : Bool
  b58 : Bool
  b59 : Bool
  b60 : Bool
  b61 : Bool
  b62 : Bool
  b63 : Bool
  b64 : Bool
deriving Veil.Enumeration

example (x : Bool64) : x ∈ Veil.Enumeration.allValues :=
  Veil.Enumeration.complete x

-- Fin fields exercise a different set of existential simplification rules.
structure Fin32 where
  f1 : Fin 2
  f2 : Fin 2
  f3 : Fin 2
  f4 : Fin 2
  f5 : Fin 2
  f6 : Fin 2
  f7 : Fin 2
  f8 : Fin 2
  f9 : Fin 2
  f10 : Fin 2
  f11 : Fin 2
  f12 : Fin 2
  f13 : Fin 2
  f14 : Fin 2
  f15 : Fin 2
  f16 : Fin 2
  f17 : Fin 2
  f18 : Fin 2
  f19 : Fin 2
  f20 : Fin 2
  f21 : Fin 2
  f22 : Fin 2
  f23 : Fin 2
  f24 : Fin 2
  f25 : Fin 2
  f26 : Fin 2
  f27 : Fin 2
  f28 : Fin 2
  f29 : Fin 2
  f30 : Fin 2
  f31 : Fin 2
  f32 : Fin 2
deriving Veil.Enumeration

example (x : Fin32) : x ∈ Veil.Enumeration.allValues :=
  Veil.Enumeration.complete x

-- Repeated parameter, function, product and option fields exercise the generic path.
structure Mixed32 (α β : Type) where
  f1 : α
  f2 : β
  f3 : Bool
  f4 : Fin 2
  f5 : Fin 2 → Bool
  f6 : α × β
  f7 : Option α
  f8 : Option β
  f9 : α
  f10 : β
  f11 : Bool
  f12 : Fin 2
  f13 : Fin 2 → Bool
  f14 : α × β
  f15 : Option α
  f16 : Option β
  f17 : α
  f18 : β
  f19 : Bool
  f20 : Fin 2
  f21 : Fin 2 → Bool
  f22 : α × β
  f23 : Option α
  f24 : Option β
  f25 : α
  f26 : β
  f27 : Bool
  f28 : Fin 2
  f29 : Fin 2 → Bool
  f30 : α × β
  f31 : Option α
  f32 : Option β
deriving Veil.Enumeration

example {α β : Type} [Veil.Enumeration α] [Veil.Enumeration β] (x : Mixed32 α β) :
    x ∈ Veil.Enumeration.allValues :=
  Veil.Enumeration.complete x

end VeilTest.Performance.DerivingEnumeration
