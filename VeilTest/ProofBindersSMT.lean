module

public import VeilTest.ActionExecution
public meta import VeilTest.ActionExecution

/-!
Dependent `assume`/`assert`/`require` must pass their proof to the continuation. Check the
generated WP bodies before SMT preprocessing, their semantics for arbitrary postconditions,
concrete executions, and both passing and failing VCs.
-/

set_option linter.unusedVariables false
set_option veil.smt.trust false
set_option veil.printCounterexamples false

open VeilTest.ActionExecution

veil module ProofBindersSMT

-- There is no zero case or default value: the proof rules that case out.
def positivePred : (n : Nat) → 0 < n → Nat
  | n + 1, _ => n

theorem positivePred_eq_sub (n : Nat) (h : 0 < n) : positivePred n h = n - 1 := by
  cases n with
  | zero => cases h
  | succ n => rfl

-- Only SMT preprocessing may erase the dependency; WP generation must retain it.
attribute [local smtSimp] positivePred_eq_sub

individual n : Nat
individual k : Nat

#gen_state

after_init {
  n := 3
  k := 0
}

action assume_pred {
  let v := k
  assume h : 0 < v
  k := positivePred v h
}

action assert_pred {
  let v := n
  assert h : 0 < v
  k := positivePred v h
}

procedure pred_required (v : Nat) {
  require h : 0 < v
  return positivePred v h
}

action require_pred {
  let v := k
  require h : 0 < v
  k := positivePred v h
}

action call_valid {
  let v ← pred_required n
  k := v
}

-- Unlike `require_pred`, this external action calls a procedure internally. The invariant
-- permits k = 0, so its caller obligation must fail instead of discarding the execution.
action call_unchecked {
  let v ← pred_required k
  k := v
}

-- Look for the existence of `positivePred v h` inside values of the listed WPs.
run_cmd do
  for name in [``assume_pred.ext.wp, ``assert_pred.ext.wp, ``pred_required.wp,
      ``require_pred.wp, ``require_pred.ext.wp, ``call_valid.ext.wp, ``call_unchecked.ext.wp] do
    let info ← Lean.getConstInfoDefn name
    -- The innermost binder is `h`
    unless (info.value.find? fun e =>
        e.isAppOfArity ``positivePred 2 && e.appArg!.hasLooseBVar 0).isSome do
      throwError "{name} lost the proof argument to positivePred"

-- Arbitrary postconditions observe the value and state produced using the bound proof.
example (handler : Int → Prop) (post : Unit → Theory → State FieldAbstractType → Prop)
    (th : Theory) (st : State FieldAbstractType) :
    assume_pred.ext.wp _ _ FieldAbstractType handler post th st =
      (∀ h : 0 < st.k, post () th { st with k := positivePred st.k h }) := by
  rfl

example (failure : Prop) (post : Unit → Theory → State FieldAbstractType → Prop)
    (th : Theory) (st : State FieldAbstractType) :
    assert_pred.ext.wp _ _ FieldAbstractType (fun _ => failure) post th st =
      (if h : 0 < st.n then post () th { st with k := positivePred st.n h } else failure) := by
  rfl

example (v : Nat) (failure : Prop) (post : Nat → Theory → State FieldAbstractType → Prop)
    (th : Theory) (st : State FieldAbstractType) :
    pred_required.wp _ _ FieldAbstractType v (fun _ => failure) post th st =
      (if h : 0 < v then post (positivePred v h) th st else failure) := by
  rfl

example (handler : Int → Prop) (post : Unit → Theory → State FieldAbstractType → Prop)
    (th : Theory) (st : State FieldAbstractType) :
    require_pred.ext.wp _ _ FieldAbstractType handler post th st =
      (∀ h : 0 < st.k, post () th { st with k := positivePred st.k h }) := by
  rfl

example (failure : Prop) (post : Unit → Theory → State FieldAbstractType → Prop)
    (th : Theory) (st : State FieldAbstractType) :
    call_unchecked.ext.wp _ _ FieldAbstractType (fun _ => failure) post th st =
      (if h : 0 < st.k then post () th { st with k := positivePred st.k h } else failure) := by
  rfl

def zero : State FieldConcreteType := { n := 3, k := 0 }
def positive : State FieldConcreteType := { n := 3, k := 2 }
def invalid : State FieldConcreteType := { n := 0, k := 2 }

#guard exactlyOneSuccess (__veil_exec_action% {} {} positive assume_pred.ext) fun _ s =>
  s.n == 3 && s.k == 1
#guard hasNoExecutions (__veil_exec_action% {} {} zero assume_pred.ext)

#guard exactlyOneSuccess (__veil_exec_action% {} {} zero assert_pred.ext) fun _ s =>
  s.n == 3 && s.k == 2
def assertFailure := __veil_exec_action% {} {} invalid assert_pred.ext
#guard assertFailure.length == 1
#guard hasAssertionFailure assertFailure fun _ s => s.n == 0 && s.k == 2

#guard exactlyOneSuccess (__veil_exec_action% {} {} positive require_pred.ext) fun _ s =>
  s.n == 3 && s.k == 1
#guard hasNoExecutions (__veil_exec_action% {} {} zero require_pred.ext)

-- The same action, when called internally, must assert its dependent requirement.
def requireFailure := __veil_exec_action% {} {} zero require_pred
#guard requireFailure.length == 1
#guard hasAssertionFailure requireFailure fun _ s => s.n == 3 && s.k == 0

#guard exactlyOneSuccess (__veil_exec_action% {} {} zero (pred_required 3)) fun v s =>
  v == 2 && s.n == 3 && s.k == 0
#guard exactlyOneSuccess (__veil_exec_action% {} {} positive call_unchecked.ext) fun _ s =>
  s.n == 3 && s.k == 1
def callFailure := __veil_exec_action% {} {} zero call_unchecked.ext
#guard callFailure.length == 1
#guard hasAssertionFailure callFailure fun _ s => s.n == 3 && s.k == 0

invariant [n_pos] n > 0
invariant [k_bounded] k < n

/-- error: This assertion might fail when called from call_unchecked -/
#guard_msgs in
#gen_spec

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  n_pos ... ✅
  k_bounded ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  require_pred
    doesNotThrow ... ✅
    n_pos ... ✅
    k_bounded ... ✅
  assume_pred
    doesNotThrow ... ✅
    n_pos ... ✅
    k_bounded ... ✅
  assert_pred
    doesNotThrow ... ✅
    n_pos ... ✅
    k_bounded ... ✅
  call_unchecked
    doesNotThrow ... ❌
    n_pos ... ✅
    k_bounded ... ✅
  call_valid
    doesNotThrow ... ✅
    n_pos ... ✅
    k_bounded ... ✅
-/
#guard_msgs in
#check_invariants

end ProofBindersSMT
