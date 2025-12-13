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
  if (sender = n) then
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

#check_invariants


#check Theory
#check State
#check FieldConcreteType
#check Label

abbrev node := Fin 5
-- abbrev foo := Fin 1
-- abbrev Guest := Guest_IndT

#check Veil.EnumerableTransitionSystem

-- simple_deriving_repr_for Theory
simple_deriving_repr_for' State


abbrev CTheory := Theory node -- foo Guest
abbrev CFieldType := FieldConcreteType node -- foo Guest
abbrev CState := State CFieldType
abbrev CLabel := Label node -- foo Guest

-- instance : Repr CTheory := inferInstance
instance : Repr CLabel := inferInstance

instance : Repr CState := inferInstance


deriving instance DecidableEq for Label
deriving instance BEq, Repr for Theory

instance : Veil.Enumeration CLabel where
  allValues := (FinEnum.ofEquiv _ (Equiv.symm (proxy_equiv% CLabel))).toList
  complete := by simp

abbrev CInit := initMultiExec CTheory CState node CFieldType -- foo Guest CFieldType
abbrev CNext := nextActMultiExec CTheory CState node -- foo Guest

/-- Extract the resulting state from an ExceptT-wrapped execution, if successful. -/
def getStateFromExceptT (c : ExceptT ε DivM (α × σ)) : Option σ :=
  match c.run with
  | .res (.ok (_, st)) => .some st
  | .res (.error _)    => .none
  | .div => none

def getAllStatesFromExceptT (c : List (ExceptT ε DivM (α × σ))) : List (Option σ) :=
  c.map getStateFromExceptT

/-- Extract all valid states from a VeilMultiExecM computation -/
def extractValidStates (exec : Veil.VeilMultiExecM κᵣ ℤ ρ σ Unit) (rd : ρ) (st : σ) : List (Option σ) :=
  exec rd st |>.map Prod.snd |> getAllStatesFromExceptT

def xx : Veil.Enumeration CLabel := inferInstance
#eval xx.allValues

@[specialize]
def enumerableTransitionSystem [labels : Veil.Enumeration CLabel] :
  Veil.EnumerableTransitionSystem
  CTheory (List CTheory)
  CState (List CState)
  CLabel
  (List (CLabel × CState)) where
  theories := [{} /-{foobar := 0}-/]
  initStates := fun th =>
    extractValidStates CInit th default |>.filterMap id
  tr := fun th st =>
    labels.allValues.flatMap (fun l =>
      (extractValidStates (CNext l) th st |>.filterMap id).map (fun next => (l, next)))

abbrev Th : CTheory := {/-foobar := 0-/ }
abbrev HTh : Th ∈ enumerableTransitionSystem.theories := by apply List.Mem.head

open Veil.ModelChecker
abbrev SearchParams : SearchParameters CTheory CState := {
  «safety» := {
    name := `single_leader
    property := fun th st => single_leader th st
    decidable := inferInstance
  }
  earlyTerminationConditions := [
    EarlyTerminationCondition.foundViolatingState
  ]
}

abbrev Hash := UInt64

-- deriving instance LawfulBEq for UInt64

-- instance : LawfulBEq UInt64 := inferInstance
-- instance : LawfulHashable UInt64 := inferInstance

-- set_option synthInstance.maxHeartbeats 1000000
-- set_option trace.Meta.synthInstance true
-- instance : Concrete.StateFingerprint CState UInt64 := inferInstance

#check Concrete.findReachable


def modelCheckerResult :=

  @Concrete.findReachable CTheory CState CLabel Hash
  (Concrete.StateFingerprint.ofHash CState)
  _ _ _ _ _ _ _
  enumerableTransitionSystem Th HTh SearchParams

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
