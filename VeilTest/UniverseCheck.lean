import Veil.Frontend.DSL.Action.Semantics.Definitions

/-! Acceptance test for the universe generalisation: `VeilM` can now be
instantiated at a state that is a `Type 1`, which is exactly the shape a
coroutine encoding needs (the state stores a suspended `NonDetT` program). -/

open Veil

abbrev Prog := NonDetT (StateT Nat DivM) Unit
abbrev St : Type 1 := Nat × Prog

/-- `VeilM` at universe 1 -/
abbrev SchedM := Veil.VeilM .external (ULift Unit) St

example : Monad SchedM := inferInstance

-- Loom's `wp` is available over it, and `SProp` is still `Prop`-valued
open PartialCorrectness DemonicChoice in
noncomputable example (act : SchedM PUnit) (post : Veil.RProp PUnit (ULift Unit) St) :
    Veil.SProp (ULift Unit) St :=
  haveI : IsHandler (fun (_ : Veil.ExIdU.{1}) => True) := ⟨⟩
  wp act post

-- and so is the transition relation
noncomputable example (act : SchedM PUnit) : Veil.Transition (ULift Unit) St :=
  Veil.VeilM.toTransition act

-- universe 0 is untouched
example : Monad (Veil.VeilM .external Unit Nat) := inferInstance
