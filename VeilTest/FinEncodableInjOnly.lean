/-
Tests for the deforested `FinEncodableInjOnly` deriving handler.

The handler generates direct arithmetic in the `encode` function (no intermediate
Sum/Sigma proxy types at runtime), while using `proxy_equiv%` only for proofs
(erased at compilation).
-/
import Veil.Frontend.DSL.State.Types

open Veil

-- ============================================================================
-- 1. Basic inductive types (no parameters)
-- ============================================================================

/-- Nullary-only (enum-like) -/
inductive Color where | red | green | blue
  deriving FinEncodableInjOnly, BEq

#eval do
  let enc (x : Color) := (FinEncodableInjOnly.encode x).val
  -- Verify encoding values
  assert! enc Color.red   == 0
  assert! enc Color.green == 1
  assert! enc Color.blue  == 2
  -- Verify card
  assert! FinEncodableInjOnly.card (κ := Color) == 3
  -- Verify injectivity: all 3 encodings are distinct
  let allEncodings := [enc Color.red, enc Color.green, enc Color.blue]
  assert! allEncodings.eraseDups.length == 3

/-- Single constructor, no fields -/
inductive MySingleton where | only
  deriving FinEncodableInjOnly

#eval do
  assert! (FinEncodableInjOnly.encode MySingleton.only).val == 0
  let inst : FinEncodableInjOnly MySingleton := inferInstance
  assert! inst.card == 1

-- ============================================================================
-- 2. Parameterized inductive types (like label types)
-- ============================================================================

/-- One parameter, mixed arities -/
inductive Action (node : Type) where
  | send (src dst : node)
  | recv (x : node)
  | timeout
  deriving FinEncodableInjOnly, BEq

#eval do
  let enc (x : Action (Fin 3)) := (FinEncodableInjOnly.encode x).val
  let card := @FinEncodableInjOnly.card (Action (Fin 3)) _
  -- card = card(Fin 3) * card(Fin 3) + card(Fin 3) + 1 = 9 + 3 + 1 = 13
  assert! card == 13
  -- send(0,0) should be first constructor, encoding = encode(0) * 3 + encode(0) = 0
  assert! enc (.send 0 0) == 0
  -- send(1,2) = encode(1) * 3 + encode(2) = 1*3 + 2 = 5
  assert! enc (.send 1 2) == 5
  -- recv(0) = 9 + encode(0) = 9
  assert! enc (.recv 0) == 9
  -- recv(2) = 9 + 2 = 11
  assert! enc (.recv 2) == 11
  -- timeout = 9 + 3 + 0 = 12
  assert! enc .timeout == 12
  -- Verify injectivity: all 13 encodings are distinct
  let allEncodings := [
    enc (.send 0 0), enc (.send 0 1), enc (.send 0 2),
    enc (.send 1 0), enc (.send 1 1), enc (.send 1 2),
    enc (.send 2 0), enc (.send 2 1), enc (.send 2 2),
    enc (.recv 0), enc (.recv 1), enc (.recv 2),
    enc .timeout]
  assert! allEncodings.eraseDups.length == 13

/-- Three fields (tests right-nested Sigma encoding) -/
inductive TripleAction (node : Type) where
  | triple (a b c : node)
  | single (x : node)
  | none_
  deriving FinEncodableInjOnly, BEq

#eval do
  let enc (x : TripleAction (Fin 2)) := (FinEncodableInjOnly.encode x).val
  let card := @FinEncodableInjOnly.card (TripleAction (Fin 2)) _
  -- card = 2*2*2 + 2 + 1 = 11
  assert! card == 11
  -- triple(0,0,0) = 0*4 + 0*2 + 0 = 0
  assert! enc (.triple 0 0 0) == 0
  -- triple(1,1,1) = 1*4 + 1*2 + 1 = 7
  assert! enc (.triple 1 1 1) == 7
  -- single(0) = 8 + 0 = 8
  assert! enc (.single 0) == 8
  -- single(1) = 8 + 1 = 9
  assert! enc (.single 1) == 9
  -- none_ = 8 + 2 + 0 = 10
  assert! enc .none_ == 10

-- ============================================================================
-- 3. Multiple parameters
-- ============================================================================

inductive TwoParam (α β : Type) where
  | left (a : α)
  | right (b : β)
  | both (a : α) (b : β)
  deriving FinEncodableInjOnly

#eval do
  let enc (x : TwoParam (Fin 2) (Fin 3)) := (FinEncodableInjOnly.encode x).val
  let card := @FinEncodableInjOnly.card (TwoParam (Fin 2) (Fin 3)) _
  -- card = 2 + 3 + 2*3 = 11
  assert! card == 11
  -- left(0) = 0, left(1) = 1
  assert! enc (.left 0) == 0
  assert! enc (.left 1) == 1
  -- right(0) = 2+0 = 2, right(2) = 2+2 = 4
  assert! enc (.right 0) == 2
  assert! enc (.right 2) == 4
  -- both(0,0) = 5+0 = 5, both(1,2) = 5+1*3+2 = 10
  assert! enc (.both 0 0) == 5
  assert! enc (.both 1 2) == 10

-- ============================================================================
-- 4. Verify typeclass properties hold
-- ============================================================================

/-- Check encode bounds and injectivity hold for a concrete type. -/
def checkProperties (α : Type) [inst : FinEncodableInjOnly α] [BEq α]
    (allValues : List α) : IO Unit := do
  -- encode < card (baked into Fin, but verify via .val)
  for a in allValues do
    assert! (inst.encode a).val < inst.card
  -- encode_inj: distinct values have distinct encodings
  let encodings := allValues.map (inst.encode ·)
  let unique := encodings.eraseDups
  assert! unique.length == encodings.length

#eval checkProperties Color [.red, .green, .blue]
#eval checkProperties (Action (Fin 2))
  [.send 0 0, .send 0 1, .send 1 0, .send 1 1, .recv 0, .recv 1, .timeout]
#eval checkProperties (TripleAction (Fin 2))
  [.triple 0 0 0, .triple 0 0 1, .triple 0 1 0, .triple 0 1 1,
   .triple 1 0 0, .triple 1 0 1, .triple 1 1 0, .triple 1 1 1,
   .single 0, .single 1, .none_]

-- ============================================================================
-- 5. Edge cases
-- ============================================================================

/-- Single constructor with one field -/
inductive Wrapper (α : Type) where
  | wrap (val : α)
  deriving FinEncodableInjOnly

#eval do
  let enc (x : Wrapper (Fin 5)) := (FinEncodableInjOnly.encode x).val
  assert! @FinEncodableInjOnly.card (Wrapper (Fin 5)) _ == 5
  assert! enc (.wrap 3) == 3

/-- Four fields (deeply nested Sigma) -/
inductive Quad (n : Type) where
  | q (a b c d : n)
  deriving FinEncodableInjOnly

#eval do
  let enc (x : Quad (Fin 2)) := (FinEncodableInjOnly.encode x).val
  let card := @FinEncodableInjOnly.card (Quad (Fin 2)) _
  assert! card == 16  -- 2^4
  -- q(0,0,0,0) = 0
  assert! enc (.q 0 0 0 0) == 0
  -- q(1,1,1,1) = 1*8 + 1*4 + 1*2 + 1 = 15
  assert! enc (.q 1 1 1 1) == 15
