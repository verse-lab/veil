module

public meta import Veil.Core.Tools.ModelChecker.Concrete.Sequential
public meta import Veil.Core.Tools.ModelChecker.Concrete.MapReduce
public meta import VeilTest.TestUtil

public meta section

/-!
For each action label, a search counts the post-states that the label generated, and the distinct
states that it reached first: those whose log entries have the label. A state with predecessors in
several chunks of a frontier is found by several workers of the parallel search in the same round;
it is still one distinct state, counted under the label of the entry that the log keeps for it.
-/

open Veil Veil.ModelChecker Veil.ModelChecker.Concrete

namespace ParallelActionStats

/-- States are the bitmasks of `nBits` bits, and label `i` sets bit `i`. A state with `d` bits set
has `d` predecessors, so the chunks of a frontier share many successors. -/
abbrev nBits := 8

instance fingerprint : StateFingerprint Nat Nat where
  beq := BEq.beq
  rfl := BEq.rfl
  eq_of_beq := LawfulBEq.eq_of_beq
  hash_eq := LawfulHashable.hash_eq
  view s := s

/-- The system, with `label i` as the label of setting bit `i`. -/
def sys {κ : Type} (label : Fin nBits → κ) :
    EnumerableTransitionSystem Unit (List Unit) Nat (List Nat) Int κ (Transitions κ Int Nat) () where
  initStates := [0]
  tr _ s := ⟨(List.finRange nBits).filterMap fun (i : Fin nBits) =>
    if s.testBit i.val then none else some (label i, s ||| (1 <<< i.val)), []⟩

def params : SearchParameters Unit Nat where
  invariants := []
  earlyTerminationConditions := []

/-- Check the statistics of a search that explored all states against the entries of its log: each
label generated a post-state from each of the `2 ^ (nBits - 1)` states without its bit, and has as
many distinct states as log entries; each state but the initial one is distinct once. -/
def check {κ : Type} [BEq κ] [Display κ] (search : String) (label : Fin nBits → κ)
    (stats : List ActionStatDisplay) (entries : List (LogEntry Nat κ)) : IO Unit := do
  let mut total := 0
  for i in List.finRange nBits do
    let stat := (stats.find? (·.label == Display.display (label i))).getD default
    let logged := entries.countP fun
      | .step _ l _ => l == label i
      | .init _ => false
    expect s!"{search}: label {i} generated {stat.statesGenerated} post-states, not {2 ^ (nBits - 1)}"
      (stat.statesGenerated == 2 ^ (nBits - 1))
    expect s!"{search}: label {i} has {stat.distinctStates} distinct states, but {logged} log entries"
      (stat.distinctStates == logged)
    total := total + stat.distinctStates
  expect s!"{search}: {total} distinct states besides the initial one, not {2 ^ nBits - 1}"
    (total == 2 ^ nBits - 1)

def checkSequential {κ : Type} {T : Type → Type} [BEq κ] [Display κ] [LabelTable κ T]
    (label : Fin nBits → κ) : IO Unit := do
  let (id, token) ← allocProgressInstance (.modelCheck {})
  let res ← breadthFirstSearchSequential (fp := fingerprint) (T := T) params (sys label) 60000 id token
  let sctx := res.val.val
  check "sequential" label (ActionStatDisplay.ofTable (κ := κ) sctx.actionStats)
    (sctx.log.toList.map Prod.snd)

def checkParallel {κ : Type} {T : Type → Type} [BEq κ] [Display κ] [LabelTable κ T]
    (label : Fin nBits → κ) (numSubTasks : Nat) : IO Unit := do
  let (id, token) ← allocProgressInstance (.modelCheck {})
  let res ← breadthFirstSearchParallel (fp := fingerprint) (T := T)
    (Shard := Std.HashMap Nat (LogEntry Nat κ)) params (sys label)
    { numSubTasks, thresholdToParallel := 1 } id token
  let mctx := res.val.val
  check s!"parallel, {numSubTasks} workers" label
    (ActionStatDisplay.ofTable (κ := κ)
      (LabelTable.zipWith (κ := κ) ActionStat.mk mctx.statesGenerated mctx.distinctStates))
    (mctx.globalSeen.toList.filterMap mctx.globalSeen.get?)

-- The statistics of `Fin nBits` labels are a vector, as for the labels of a Veil module, which have
-- `FinEncodableInjOnly` instances; those of `Nat` labels are a hash map.
#eval do
  checkSequential (κ := Fin nBits) id
  checkSequential (κ := Nat) Fin.val
  for numSubTasks in [1, 2, 3, 4, 8] do
    checkParallel (κ := Fin nBits) id numSubTasks
    checkParallel (κ := Nat) Fin.val numSubTasks

end ParallelActionStats
