module

public import VeilTest.ActionExecution
public meta import VeilTest.ActionExecution

/-!
Proof binders: `require h : p`, `assert h : p`, `assume h : p`, `let x :| h : p` and
`if x :| h : p` (with and without a witness type, and with a tuple witness), plus the dependent
`if h : p`. The proofs are used where Lean needs them (indexing, `List.head`, `Option.get`). Each
action is executed concretely, its WP is generated, and the module is model checked.
`ProofBindersSMT.lean` checks dependent WPs and the VCs with the SMT solver.

NOTE: Every proposition is stated over a local copy such as `let l := items`, not over the field itself,
because of a limitation not lifted yet: each statement reads the state again and rebinds the field
names, so a proof is about the field as its own statement read it. In

```
require h : items ≠ []
picked := items.head h
```

`h` is about the `items` that the `require` read, while the assignment reads `items` again. The two
reads *are bound to different variables* due to Veil's DSL elaboration,
which are not definitionally equal even though nothing in
between writes `items`, so `h` has type `items✝ ≠ []` where `items ≠ []` is expected. A local such
as `l` stays the same variable across statements.
-/

set_option linter.unusedVariables false

open VeilTest.ActionExecution

veil module ProofBinders

individual items : List Nat
individual msgs : List (Option Nat)
individual picked : Nat

#gen_state

after_init {
  items := [10, 20, 30]
  msgs := [none, some 7]
  picked := 0
}

/- Called by another action, `require` asserts. -/
procedure read_at (i : Nat) {
  let l := items
  require h : i < l.length
  picked := l[i]
  return picked
}

action read_first {
  let n ← read_at 0
  return n
}

procedure read_out_of_range {
  let n ← read_at 5
  return n
}

/- Called by the environment, `require` assumes. -/
action require_head {
  let l := items
  require h : l ≠ []
  picked := l.head h
}

procedure assert_head {
  let l := items
  assert h : l ≠ []
  picked := l.head h
  return picked
}

/- The proof about the picked message replaces a total accessor with a dead default. -/
action receive {
  let m :| m ∈ msgs
  assume h : m.isSome
  picked := m.get h
}

action pick_index {
  let l := items
  let i : Fin 3 :| h : i.val < l.length
  picked := l[i.val]
}

action pick_index_if {
  let l := items
  if i : Fin 3 :| h : i.val < l.length then
    picked := l[i.val]
  else
    picked := 0
}

action read_if (far : Bool) {
  let l := items
  let i := if far then 7 else 1
  if h : i < l.length then
    picked := l[i]
  else
    picked := 0
}

/- Called by the environment, a `require` that fails rules the execution out: the model checker
below must not report it as an assertion failure. -/
action require_too_long {
  let l := items
  require h : 5 < l.length
  picked := l[5]
}

action pick_member {
  let ms := msgs
  let m :| h : m ∈ ms
  picked := (ms.head (List.ne_nil_of_mem h)).getD 0
}

action pick_flag_if {
  let p := picked
  if b :| h : b = (p == 0) then
    let hb : b = (p == 0) := h
    picked := if b then 1 else 2
  else
    picked := 0
}

action pick_pair {
  let (a, b) : Bool × Bool :| h : a = true ∧ b = false
  let ha : a = true := h.1
  picked := if a then 1 else 2
}

action pick_pair_if {
  if (a, b) : Bool × Bool :| h : a = true ∧ b = false then
    let ha : a = true := h.1
    picked := if a then 1 else 2
  else
    picked := 0
}

/--
warning: local `picked` shadows mutable state component `picked`; references to this name resolve to the local
-/
#guard_msgs(warning) in
procedure require_shadow_warns {
  let l := items
  require picked : l ≠ []
  return l.head picked
}

def initial : State FieldConcreteType := { items := [10, 20, 30], msgs := [none, some 7], picked := 0 }
def empty : State FieldConcreteType := { items := [], msgs := [], picked := 1 }

#guard exactlyOneSuccess (__veil_exec_action% {} {} initial read_first) fun n s =>
  n == 10 && s.picked == 10
#guard hasAssertionFailure (__veil_exec_action% {} {} initial read_out_of_range) fun _ s =>
  s.picked == 0

#guard exactlyOneSuccess (__veil_exec_action% {} {} initial require_head) fun _ s => s.picked == 10
-- `__veil_exec_action%` runs actions as internal calls, where `require` asserts.
#guard hasAssertionFailure (__veil_exec_action% {} {} empty require_head) fun _ s => s.picked == 1

#guard exactlyOneSuccess (__veil_exec_action% {} {} initial assert_head) fun n s =>
  n == 10 && s.picked == 10
#guard hasAssertionFailure (__veil_exec_action% {} {} empty assert_head) fun _ s => s.picked == 1

#guard exactlyOneSuccess (__veil_exec_action% {} {} initial receive) fun _ s => s.picked == 7

#guard exactlyNSuccesses 3 (__veil_exec_action% {} {} initial pick_index) fun _ s =>
  [10, 20, 30].contains s.picked
#guard hasNoExecutions (__veil_exec_action% {} {} empty pick_index)

#guard exactlyNSuccesses 3 (__veil_exec_action% {} {} initial pick_index_if) fun _ s =>
  [10, 20, 30].contains s.picked
#guard exactlyOneSuccess (__veil_exec_action% {} {} empty pick_index_if) fun _ s => s.picked == 0

#guard exactlyOneSuccess (__veil_exec_action% {} {} initial (read_if false)) fun _ s => s.picked == 20
#guard exactlyOneSuccess (__veil_exec_action% {} {} initial (read_if true)) fun _ s => s.picked == 0

#guard exactlyNSuccesses 2 (__veil_exec_action% {} {} initial pick_member) fun _ s => s.picked == 0
#guard hasNoExecutions (__veil_exec_action% {} {} empty pick_member)

#guard exactlyOneSuccess (__veil_exec_action% {} {} initial pick_flag_if) fun _ s => s.picked == 1
#guard exactlyOneSuccess (__veil_exec_action% {} {} empty pick_flag_if) fun _ s => s.picked == 2

#guard exactlyOneSuccess (__veil_exec_action% {} {} initial pick_pair) fun _ s => s.picked == 1
#guard exactlyOneSuccess (__veil_exec_action% {} {} initial pick_pair_if) fun _ s => s.picked == 1

#guard exactlyOneSuccess (__veil_exec_action% {} {} initial require_shadow_warns) fun n _ => n == 10

invariant [picked_bounded] picked ≤ 30

#gen_spec

/-- info: ✅ No violation (explored 7 states) -/
#guard_msgs in
#model_check interpreted { } { }

end ProofBinders
