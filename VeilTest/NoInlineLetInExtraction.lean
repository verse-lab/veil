import VeilTest.ActionExecution

set_option linter.unusedVariables false

/-!
Extraction must preserve sharing of ordinary value lets and the join points
that Lean's `do` elaborator uses for branch continuations. Inlining join points
makes the extracted term grow exponentially in the number of sequential branches.

These tests check the extracted structure and execution results: marker literals
must occur once in the expanded tree, and source join points must retain let bindings.
-/

open Lean VeilTest.ActionExecution

namespace VeilTest.NoInlineLetInExtraction

/-- Count occurrences in the expanded tree, caching counts of shared subterms.
`Expr.forEach` would visit each distinct subterm only once, hiding duplication. -/
private partial def countLit (lit : Nat) (e₀ : Expr) : Nat := (go e₀).run' {}
where
  go (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
    if let some n := (← get).get? e then return n
    -- `nat?` matches OfNat applications, not the raw literal repeated in their instances.
    let n ← e.foldlM (fun n child => return n + (← go child))
      (if e.nat? == some lit then 1 else 0)
    modify (·.insert e n)
    return n

/-- Count let binders once per distinct subterm, optionally restricting to `do` join points. -/
private def countLets (e : Expr) (joinPointsOnly := false) : IO Nat := do
  let count ← IO.mkRef 0
  e.forEach fun e => do
    if let .letE nm .. := e then
      if !joinPointsOnly || nm.eraseMacroScopes == `__do_jp then
        count.modify (· + 1)
  count.get

open Elab Command in
/-- Check that the extracted function keeps at least one let per source join point. -/
elab "#assert_join_points_shared " act:ident " in " ext:ident : command => do
  let expected ← countLets (← getConstInfoDefn act.getId).value (joinPointsOnly := true)
  if expected == 0 then
    throwError "{act.getId} binds no join point, so this test would prove nothing"
  let actual ← countLets (← getConstInfoDefn ext.getId).value
  unless actual ≥ expected do
    throwError "extraction inlined join points: {ext.getId} has {actual} `let`(s) \
      but {act.getId} binds {expected} join point(s)"

open Elab Command in
/-- Check that a marker literal occurs exactly once in the expanded extracted term. -/
elab "#assert_occurs_once " lit:num " in " ext:ident : command => do
  let n := countLit lit.getNat (← getConstInfoDefn ext.getId).value
  unless n == 1 do
    throwError "literal {lit.getNat} occurs {n} time(s) in {ext.getId}, expected 1"

open Elab Command in
/-- Guard against term growth beyond what the marker and let checks detect. -/
elab "#assert_tree_size_below " bound:num " in " ext:ident : command => do
  let n := (← getConstInfoDefn ext.getId).value.sizeWithoutSharing
  unless n < bound.getNat do
    throwError "{ext.getId} has tree size {n}, expected below {bound.getNat}"

end VeilTest.NoInlineLetInExtraction

open VeilTest.NoInlineLetInExtraction

/-! ### Six sequential branches in one action

Without join point sharing this action's extracted form doubles in size for each
`if`, and `marker` below appears `2^5` times instead of once. -/

veil module JoinPointSharingSequential

type node
immutable individual flag : Bool
individual counter : Nat

#gen_state

after_init { counter := 0 }

action step (n : node) {
  if flag then counter := counter + 1
  if flag then counter := counter + 2
  if flag then counter := counter + 3
  if flag then counter := counter + 4
  if flag then counter := counter + 5
  if flag then counter := counter + 90001
}

safety [nonneg] counter ≥ 0

#gen_spec

#guard_msgs (drop info) in
#model_check interpreted { node := Unit } { flag := false }

#assert_join_points_shared JoinPointSharingSequential.step.ext
  in JoinPointSharingSequential.step.ext.extracted
#assert_occurs_once 90001 in JoinPointSharingSequential.step.ext.extracted
#assert_tree_size_below 40000 in JoinPointSharingSequential.step.ext.extracted

end JoinPointSharingSequential

/-! ### Join points hidden behind state reads

Here each branch condition reads mutable state, so the join point is preceded by
the `let`s Veil generates for the read. Those have to be stepped past one at a
time: reducing the whole chain at once takes the join point with it. -/

veil module JoinPointSharingBehindStateReads

type node
immutable individual flag : Bool
individual counter : Nat

#gen_state

after_init { counter := 0 }

action step (n : node) {
  require flag
  if flag then
    require counter > 0
  if counter > 1 then
    counter := counter + 1
  else if counter > 2 then
    counter := counter + 2
  else
    counter := counter + 3
  counter := counter + 90002
  if flag then
    require counter > 5
}

safety [nonneg] counter ≥ 0

#gen_spec

#guard_msgs (drop info) in
#model_check interpreted { node := Unit } { flag := false }

#assert_join_points_shared JoinPointSharingBehindStateReads.step.ext
  in JoinPointSharingBehindStateReads.step.ext.extracted
#assert_occurs_once 90002 in JoinPointSharingBehindStateReads.step.ext.extracted
#assert_tree_size_below 20000 in JoinPointSharingBehindStateReads.step.ext.extracted

end JoinPointSharingBehindStateReads

/-! ### Reassigned mutable locals

Each join point receives the branch result plus the reassigned locals. The
first action has two-argument joins; the second mixes three-argument joins
(`Unit`, `Nat`, `Bool`) with a two-argument join. -/

veil module JoinPointSharingOneMutableLocal

immutable individual flag : Bool
individual counter : Nat

#gen_state

after_init { counter := 0 }

action step {
  let mut x := 0
  if flag then x := x + 1
  if flag then x := x + 2
  if flag then x := x + 3
  counter := x + 90003
}

safety [nonneg] counter ≥ 0

#gen_spec

#guard_msgs (drop info) in
#model_check interpreted { } { flag := false }

#assert_join_points_shared JoinPointSharingOneMutableLocal.step.ext
  in JoinPointSharingOneMutableLocal.step.ext.extracted
#assert_occurs_once 90003 in JoinPointSharingOneMutableLocal.step.ext.extracted
#assert_tree_size_below 10000 in JoinPointSharingOneMutableLocal.step.ext.extracted

#guard exactlyOneSuccess (__veil_exec_action% {} { flag := true } { counter := 0 } step)
  fun _ state => state.counter == 90009

#guard exactlyOneSuccess (__veil_exec_action% {} { flag := false } { counter := 0 } step)
  fun _ state => state.counter == 90003

end JoinPointSharingOneMutableLocal

/-!
Reassigning `x : Nat` and `b : Bool` produces joins with two or three parameters
(`Unit` plus the reassigned locals). Check that extraction preserves sharing
and threads the locals correctly for both values of `flag`.
-/

veil module JoinPointSharingMultipleMutableLocals

immutable individual flag : Bool
individual counter : Nat

#gen_state

after_init { counter := 0 }

action step {
  let mut x := 0
  let mut b := false
  if flag then
    x := x + 1
    b := true
  if b then x := x + 2
  if flag then
    x := x + 3
    b := false
  else
    x := x + 4
    b := true
  counter := x + (if b then 10 else 20) + 90004
}

safety [nonneg] counter ≥ 0

#gen_spec

#guard_msgs (drop info) in
#model_check interpreted { } { flag := false }

#assert_join_points_shared JoinPointSharingMultipleMutableLocals.step.ext
  in JoinPointSharingMultipleMutableLocals.step.ext.extracted
#assert_occurs_once 90004 in JoinPointSharingMultipleMutableLocals.step.ext.extracted
#assert_tree_size_below 15000 in JoinPointSharingMultipleMutableLocals.step.ext.extracted

#guard exactlyOneSuccess (__veil_exec_action% {} { flag := true } { counter := 0 } step)
  fun _ state => state.counter == 90030

#guard exactlyOneSuccess (__veil_exec_action% {} { flag := false } { counter := 0 } step)
  fun _ state => state.counter == 90018

end JoinPointSharingMultipleMutableLocals

/-!
Use a Veil procedure as a zero-arity local program, called before, inside, and
after nested branches. Each call must read the state written by previous calls.
Veil rejects deferred `let program := do ...` blocks, so `delta%` exposes the
procedure body at the local let. This lets the marker check detect duplication
of the body instead of merely checking a reference to its extraction certificate.
-/

veil module JoinPointSharingZeroArity

immutable individual flag : Bool
individual counter : Nat
individual last : Nat

#gen_state

after_init { counter := 0; last := 0 }

procedure advance {
  assume counter < 10
  if counter % 2 = 0 then
    counter := counter + 1
  else
    counter := counter + 2
  last := 90013
}

action step {
  let program := delta% advance
  program
  if flag then
    program
    if counter < 6 then program
  else
    counter := counter + 1
    program
  program
}

safety [nonneg] counter ≥ 0

#gen_spec

#guard_msgs (drop info) in
#model_check interpreted {} { flag := false }

#assert_join_points_shared JoinPointSharingZeroArity.step.ext
  in JoinPointSharingZeroArity.step.ext.extracted
#assert_occurs_once 90013 in JoinPointSharingZeroArity.step.ext.extracted
#assert_tree_size_below 20000 in JoinPointSharingZeroArity.step.ext.extracted

#guard exactlyOneSuccess (__veil_exec_action% {} { flag := true } { counter := 0, last := 0 } step)
  fun _ state => state.counter == 7 && state.last == 90013
#guard exactlyOneSuccess (__veil_exec_action% {} { flag := false } { counter := 0, last := 0 } step)
  fun _ state => state.counter == 5 && state.last == 90013
#guard exactlyOneSuccess (__veil_exec_action% {} { flag := true } { counter := 4, last := 0 } step)
  fun _ state => state.counter == 9 && state.last == 90013
#guard hasNoExecutions (__veil_exec_action% {} { flag := true } { counter := 8, last := 0 } step)
#guard hasNoExecutions (__veil_exec_action% {} { flag := false } { counter := 8, last := 0 } step)

end JoinPointSharingZeroArity

/-!
Repeat the local-program test with `Nat` and `Bool` parameters. Calls in different
branches pass different arguments; later calls must see both those arguments and
the updated state. The nested conditional is exercised in both directions.
-/

veil module JoinPointSharingParameterizedProgram

immutable individual flag : Bool
individual counter : Nat
individual last : Nat

#gen_state

after_init { counter := 0; last := 0 }

procedure advance (amount : Nat) (twice : Bool) {
  assume counter < 10
  if twice then counter := counter + amount
  counter := counter + amount
  last := 90014
}

action step {
  let program := delta% advance
  program 1 false
  if flag then
    program 2 true
    if counter < 8 then program 1 false
  else
    program 3 false
  program 2 flag
}

safety [nonneg] counter ≥ 0

#gen_spec

#guard_msgs (drop info) in
#model_check interpreted {} { flag := false }

#assert_join_points_shared JoinPointSharingParameterizedProgram.step.ext
  in JoinPointSharingParameterizedProgram.step.ext.extracted
#assert_occurs_once 90014 in JoinPointSharingParameterizedProgram.step.ext.extracted
#assert_tree_size_below 20000 in JoinPointSharingParameterizedProgram.step.ext.extracted

#guard exactlyOneSuccess (__veil_exec_action% {} { flag := true } { counter := 0, last := 0 } step)
  fun _ state => state.counter == 10 && state.last == 90014
#guard exactlyOneSuccess (__veil_exec_action% {} { flag := false } { counter := 0, last := 0 } step)
  fun _ state => state.counter == 6 && state.last == 90014
#guard exactlyOneSuccess (__veil_exec_action% {} { flag := true } { counter := 3, last := 0 } step)
  fun _ state => state.counter == 12 && state.last == 90014
#guard hasNoExecutions (__veil_exec_action% {} { flag := true } { counter := 8, last := 0 } step)
#guard hasNoExecutions (__veil_exec_action% {} { flag := false } { counter := 8, last := 0 } step)

end JoinPointSharingParameterizedProgram

/-! ### Ordinary value lets and extraction edge cases -/

veil module LetSharingAdditionalCases

immutable individual flag : Bool
individual left : Nat
individual right : Nat
individual bit : Bool

#gen_state

after_init { left := 0; right := 0; bit := true }

-- A value used twice must remain shared even without a join point.
action value {
  let x := 1 + 90011
  left := x
  right := x
}

-- Nested value lets must survive around a join carrying a reassigned local.
action nested_value {
  let mut x := 90012
  let y := x + 1
  if flag then x := x + 2
  let z := x + y
  left := z
  right := z
}

-- The body relies on α's definition: `false` cannot have an arbitrary type α.
action type_let {
  let α := Bool
  let x : α := false
  bit := x
}

safety [paired] left = right

#gen_spec

#guard_msgs (drop info) in
#model_check interpreted {} { flag := false }

#assert_occurs_once 90011 in LetSharingAdditionalCases.value.ext.extracted
#assert_occurs_once 90012 in LetSharingAdditionalCases.nested_value.ext.extracted
#assert_join_points_shared LetSharingAdditionalCases.nested_value.ext
  in LetSharingAdditionalCases.nested_value.ext.extracted

def initial : State FieldConcreteType := { left := 0, right := 0, bit := true }

#guard exactlyOneSuccess (__veil_exec_action% {} { flag := false } initial value)
  fun _ state => state.left == 90012 && state.right == 90012 && state.bit
#guard exactlyOneSuccess (__veil_exec_action% {} { flag := true } initial nested_value)
  fun _ state => state.left == 180027 && state.right == 180027 && state.bit
#guard exactlyOneSuccess (__veil_exec_action% {} { flag := false } initial nested_value)
  fun _ state => state.left == 180025 && state.right == 180025 && state.bit
#guard exactlyOneSuccess (__veil_exec_action% {} { flag := false } initial type_let)
  fun _ state => !state.bit && state.left == 0 && state.right == 0

/-!
These lower-level tests supply explicit join points and certificate hypotheses
that ordinary action elaboration does not generate. Keep them together rather
than changing their source shape to fit the action frontend.
-/
section ExtractionInternals

open Veil Veil.Extract MultiExtractor

-- Exercise Loom's default tactic, whose simplification between steps must
-- retain value lets just as Veil's custom extraction loop does.
def defaultTacticValueLet (n : Nat) : VeilMultiExecM Std.Format Int Unit Nat Nat :=
  veil_dsimp% -zeta -failIfUnchanged [multiExtractSimp, NonDetT.extractList]
    (NonDetT.extractList Std.Format (VeilExecM .internal Unit Nat) _
      (let x := n + 90015; pure (x + x)))

#assert_occurs_once 90015 in LetSharingAdditionalCases.defaultTacticValueLet
#guard extractAllResults (defaultTacticValueLet 1) () 0 == [.success 180032 0]

def zeroAritySource (flag : Bool) : VeilM .internal Unit Nat Nat :=
  let jp : VeilM .internal Unit Nat Nat := pure 90005
  if flag then jp else jp

def zeroArityExtracted (flag : Bool) : VeilMultiExecM Std.Format Int Unit Nat Nat :=
  veil_dsimp% -zeta -failIfUnchanged [multiExtractSimp, NonDetT.extractList]
    (NonDetT.extractList Std.Format _ _ (delta% zeroAritySource flag)
      (h := by veil_extract_list_tactic))

#assert_occurs_once 90005 in LetSharingAdditionalCases.zeroArityExtracted
#guard extractAllResults (zeroArityExtracted true) () 0 == [.success 90005 0]
#guard extractAllResults (zeroArityExtracted false) () 0 == [.success 90005 0]

def dependentSource (flag : Bool) : VeilM .internal Unit Nat Nat :=
  let jp := fun (n : Nat) (i : Fin (n + 1)) (_h : n = n) =>
    (pure (i.val + 90006) : VeilM .internal Unit Nat Nat)
  if flag then jp 2 1 rfl else jp 3 2 rfl

def dependentExtracted (flag : Bool) : VeilMultiExecM Std.Format Int Unit Nat Nat :=
  veil_dsimp% -zeta -failIfUnchanged [multiExtractSimp, NonDetT.extractList]
    (NonDetT.extractList Std.Format _ _ (delta% dependentSource flag)
      (h := by veil_extract_list_tactic))

#assert_occurs_once 90006 in LetSharingAdditionalCases.dependentExtracted
#guard extractAllResults (dependentExtracted true) () 0 == [.success 90007 0]
#guard extractAllResults (dependentExtracted false) () 0 == [.success 90008 0]

/-! ### Looking up local join-point certificates

Skip inapplicable hypotheses and continue to the matching certificate. Merely
substituting arguments into a hypothesis's type does not validate its application.
-/

-- Both hypotheses have one parameter, but `hbad` cannot accept `0 : Nat`.
-- Constructing `hbad 0` with `mkAppN` used to pass the source check and fail
-- only when the kernel checked the resulting extraction certificate.
example (jpS : Nat → VeilM .internal Unit Nat Nat)
    (jpT : Nat → VeilMultiExecM Std.Format Int Unit Nat Nat)
    (hbad : ∀ _ : Bool, ExtractConstraint Std.Format (VeilExecM .internal Unit Nat)
      (VeilMultiExecM Std.Format Int Unit Nat) (findOfCandidates _) (jpS 0) (jpT 0))
    (hgood : ∀ n, ExtractConstraint Std.Format (VeilExecM .internal Unit Nat)
      (VeilMultiExecM Std.Format Int Unit Nat) (findOfCandidates _) (jpS n) (jpT n)) :
    ConstrainedExtractResult Std.Format (VeilExecM .internal Unit Nat)
      (VeilMultiExecM Std.Format Int Unit Nat) (findOfCandidates _) (jpS 0) := by
  extract_let_step

-- Here the argument type matches, but the first certificate relates a different
-- source. Rejecting it while constructing the result must not end the search.
example (jpS other : Nat → VeilM .internal Unit Nat Nat)
    (jpT otherT : Nat → VeilMultiExecM Std.Format Int Unit Nat Nat)
    (hother : ∀ n, ExtractConstraint Std.Format (VeilExecM .internal Unit Nat)
      (VeilMultiExecM Std.Format Int Unit Nat) (findOfCandidates _) (other n) (otherT n))
    (hgood : ∀ n, ExtractConstraint Std.Format (VeilExecM .internal Unit Nat)
      (VeilMultiExecM Std.Format Int Unit Nat) (findOfCandidates _) (jpS n) (jpT n)) :
    ConstrainedExtractResult Std.Format (VeilExecM .internal Unit Nat)
      (VeilMultiExecM Std.Format Int Unit Nat) (findOfCandidates _) (jpS 0) := by
  extract_let_step

-- This transformation is opt-in through multiExtractSimp, never a default
-- procedure of ordinary `dsimp`.
run_cmd Elab.Command.liftTermElabM do
  let name := ``simpExtractedValueLet
  if (← Meta.Simp.getSimprocs).simprocNames.contains name then
    throwError "value-let projection simproc is registered globally"
  let some ext ← Meta.Simp.getSimprocExtension? `multiExtractSimp
    | throwError "multiExtractSimp has no simproc extension"
  unless (← ext.getSimprocs).simprocNames.contains name do
    throwError "multiExtractSimp is missing the value-let projection simproc"

end ExtractionInternals

end LetSharingAdditionalCases
