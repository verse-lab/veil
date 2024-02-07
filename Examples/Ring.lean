import LeanSts.State
import LeanSts.TransitionSystem
import Mathlib.Tactic
import Mathlib.Testing.SlimCheck.Testable
import Mathlib.Testing.SlimCheck.Sampleable
import Mathlib.Testing.SlimCheck.Functions
import Mathlib.Testing.SlimCheck.Gen


section Ring

structure RingStructure (node : Type) :=
  -- TODO: need to somehow mark these as immutable
  -- relation
  le (x y : node) : Bool
  -- axioms: le is a total order
  -- le_refl       (x : node) : le x x
  -- le_trans  (x y z : node) : le x y → le y z → le x z
  -- le_antisymm (x y : node) : le x y → le y x → x = y
  -- le_total    (x y : node) : le x y ∨ le y x

  -- relation: btw represents a ring
  btw (w x y : node) : Bool
  -- axioms
  -- btw_ring    (x y z : node) : btw x y z → btw y z x
  -- btw_trans (w x y z : node) : btw w x y → btw w y z → btw w x z
  -- btw_side    (w x y : node) : btw w x y → ¬ btw w y x
  -- btw_total   (w x y : node) : btw w x y ∨ btw w y x ∨ w = x ∨ w = y ∨ x = y

  -- actual state
  -- leader (n : node) : Bool
  -- pending (n1 n2 : node) : Bool

-- #sample Bool
-- #sample Nat
-- #sample Bool × Nat
-- #sample (Nat → Nat → Bool)
-- #sample (Fin 4)

open SlimCheck SlimCheck.Gen

-- instance Ring.sampleableExt [SampleableExt α] : SampleableExt (RingStructure α) :=
--   SampleableExt.mkSelfContained do
--     let le ← SampleableExt.sample (α → α → Bool)
--     let btw ← SampleableExt.sample (α → α → α → Bool)
--     pure ⟨le, btw⟩

-- open SampleableExt
-- instance Ring.sampleableExt [SampleableExt α] : SampleableExt (RingStructure α) where
--   proxy := Prod (SampleableExt.proxy α → α → Bool) (SampleableExt.proxy α → α → α → Bool)
--   interp f := ⟨fun _ _ => false, fun _ _ _ => false⟩
--   sample := do







-- #sample RingStructure (Fin 5)

-- example : ∃ r : RingStructure (Fin 5), True := by
--  slim_check




end Ring
