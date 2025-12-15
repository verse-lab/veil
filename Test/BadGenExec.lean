import Veil
import Veil.Core.Tools.ModelChecker.TransitionSystem
import Veil.Core.Tools.ModelChecker.Interface
import Veil.Core.Tools.ModelChecker.Concrete.Checker
import Mathlib.Data.FinEnum
import Mathlib.Tactic.ProxyType

-- https://github.com/aman-goel/ivybench/blob/5db7eccb5c3bc2dd14dfb58eddb859b036d699f5/ex/ivy/ring.ivy

set_option trace.veil.desugar true

veil module Ring

type node
-- type foo

-- inductive Action (node : Type) where
--   | send (n next : node)
--   | recv (sender n next : node)
-- deriving Inhabited, Ord, Lean.ToJson, Hashable, BEq, Repr

immutable function baaaa : node → node → Nat


instantiate tot : TotalOrder node
instantiate btwn : Between node
-- -- set_option synthInstance.maxHeartbeats 200000ʡ
-- -- FIXME: importing `ModelChecker.TransitionSystem` causes this to break???
-- -- It was because of `class abbrev Collection`
-- enum Guest = {Olivier, Bruno, Aquinas}

-- instance : Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord Guest_IndT))) :=
--  by apply Std.LawfulEqCmp.mk; decide

open Between TotalOrder


-- immutable individual foobar : foo

-- individual log : List (Action node)
relation leader : node -> Bool
relation pending : node -> node -> Bool
-- relation pendingfff : node → foo → Bool
-- NOTE: this causes the issue with deriving the FieldRepresentation and
-- LawfulFieldRepresentation instances commenting it out makes this file compile
-- successfully
-- function zz : node → foo → node → node
#time #gen_state

after_init {
  -- log := []
  leader N := false
  pending M N := false
}

action send (n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  -- log := log ++ [Action.send n next]
  pending n next := true
}

action recv (sender n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  -- log := log ++ [Action.recv sender n next]
  -- message may or may not be removed
  -- this models that multiple messages might be in flight
  let b ← pick Bool
  pending sender n := b  -- FIXME: `pending sender n := *` has bad execution performance
  if (n = n) then
    leader n := true
  else
    -- pass message to next node
    if (le n sender) then
      pending sender next := true
}

-- action nondet_log  {
--   log := *
-- }


safety [single_leader] leader N ∧ leader M → N = M
invariant [leader_greatest] leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#gen_spec


open Veil.ModelChecker
-- abbrev SearchParams : SearchParameters (Theory (Fin 5)) (State (FieldConcreteType (Fin 5))) :=

def modelCheckerResult :=
  Concrete.findReachable
  (enumerableTransitionSystem (Fin 5) {baaaa := fun _ _ => 0})
  {
  «safety» := {
    name := `single_leader
    property := fun th st => single_leader th st
  }
  earlyTerminationConditions := [
    -- EarlyTerminationCondition.foundViolatingState,
    -- EarlyTerminationCondition.reachedDepthBound 4
  ]
  }

-- def modelCheckerResult :=
--   @Concrete.findReachable CTheory CState CLabel Hash
--   (Concrete.StateFingerprint.ofHash CState)
--   _ _ _ _ _ _
--   enumerableTransitionSystem Th HTh SearchParams

#time #eval! modelCheckerResult


  -- Concrete.findReachable enumerableTransitionSystem Th HTh SearchParams

-- #time #finitize_types (Fin 5), (Fin 3), Guest_IndT
-- #set_theory { foobar := 0 }

-- #time #model_check single_leader
-- #eval spaceSize modelCheckerResult

-- open ProofWidgets
-- open scoped ProofWidgets.Jsx
-- #html <ModelCheckerView trace={statesJson} layout={"vertical"} />

end Ring
