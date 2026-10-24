module

public import Veil

/-!
A counterexample trace shows, under the header of each state, the candidates picked on the way to
it (`choices:`), in order; for the initial state, those of the initializer. Each is shown as
`x = v`, with `x` what the pick is bound to: the variable of `let x ← pick τ` or `let x :| p`, also
inside a called procedure, or the target of a havoc `x := *`. A state reached without picks has no
`choices:` line. The choices are looked up at the positions of the trace's transitions
that the search log records, which the parallel and the sequential search write differently. The
shortest counterexample below is unique, so both must find it, with the same choices.

The initializer and actions share a picking procedure. `step` calls a procedure that calls another
procedure, with nested `if`s in both the action and the callee. Picks before, inside and after those
calls must appear in execution order, without picks from untaken branches. `finish` adds a pick
filtered by `require` and a constrained pick; their logs must stay separate from those of `step`.
-/

veil module TraceChoices

individual enabled : Bool
individual approved : Bool
individual phase : Nat
individual score : Nat

#gen_state

procedure choose_flag {
  let flag ← pick Bool
  return flag
}

after_init {
  enabled ← choose_flag
  approved := true
  phase := 0
  score := 0
}

procedure choose_bonus {
  let high ← choose_flag
  if high then
    let bonus ← pick (Fin 3)
    if bonus.val = 2 then
      approved ← choose_flag
    else
      approved := true
    return bonus.val
  else
    let bonus ← pick (Fin 2)
    approved := true
    return bonus.val
}

procedure apply_bonus (base : Nat) {
  let bonus ← choose_bonus
  score := base + bonus
  return approved
}

action arm {
  require phase = 0
  phase := 1
}

action step {
  require phase = 1
  let base ← pick (Fin 3)
  if base.val = 2 then
    -- The condition logs the nested calls' picks and updates both `approved` and `score`.
    if (← apply_bonus base.val) then
      let reset ← pick (Fin 2)
      score := reset.val
    else
      let extra ← pick (Fin 2)
      score := score + extra.val
  else
    approved ← choose_flag
    score := base.val
  phase := 2
}

action finish {
  require phase = 2
  if enabled then
    if approved then
      let reset ← pick (Fin 2)
      score := reset.val
    else
      let confirmed ← choose_flag
      require confirmed
      let tag : Fin 3 :| tag.val = 2
      score := score + tag.val
  else
    let reset ← pick (Fin 2)
    score := reset.val
  phase := 3
}

safety ¬ (phase = 3 ∧ enabled ∧ ¬ approved ∧ score = 7)

#gen_spec

/--
error: ❌ Violation: safety_failure (violates: safety_0)
  State 0 (via init):
    choices: flag = true
    enabled = true
    approved = true
    phase = 0
    score = 0
  State 1 (via arm):
    enabled = true
    approved = true
    phase = 1
    score = 0
  State 2 (via step):
    choices: base = 2, flag = true, bonus = 2, flag = false, extra = 1
    enabled = true
    approved = false
    phase = 2
    score = 5
  State 3 (via finish):
    choices: flag = true, tag = 2
    enabled = true
    approved = false
    phase = 3
    score = 7
-/
#guard_msgs in
#model_check interpreted {} {}

/--
error: ❌ Violation: safety_failure (violates: safety_0)
  State 0 (via init):
    choices: flag = true
    enabled = true
    approved = true
    phase = 0
    score = 0
  State 1 (via arm):
    enabled = true
    approved = true
    phase = 1
    score = 0
  State 2 (via step):
    choices: base = 2, flag = true, bonus = 2, flag = false, extra = 1
    enabled = true
    approved = false
    phase = 2
    score = 5
  State 3 (via finish):
    choices: flag = true, tag = 2
    enabled = true
    approved = false
    phase = 3
    score = 7
-/
#guard_msgs in
#model_check interpreted {} {} (sequential := true)

end TraceChoices

/-!
A state constraint drops some results of a pick, which moves the later ones: below, the result of
`k = 2` is the second transition of `step` that the search sees, not the third. The choices must
still be those of the transition that the trace takes.
-/

veil module TraceChoicesStateConstraint

individual x : Nat

#gen_state

after_init {
  x := 0
}

action step {
  let k ← pick (Fin 3)
  x := k.val
}

safety x < 2

state_constraint [skip_one] x ≠ 1

#gen_spec

/--
error: ❌ Violation: safety_failure (violates: safety_0)
  State 0 (via init):
    x = 0
  State 1 (via step):
    choices: k = 2
    x = 2
-/
#guard_msgs in
#model_check interpreted {} {}

end TraceChoicesStateConstraint

/-!
An assertion failure has an extra, failing step. Its choices include the picks before the assertion
and exclude those after it. The only failing route is `prepare` picking `2, true`, followed by
`check` picking `true, 1`. The initializer's pick is filtered by `require`.
-/

veil module TraceChoicesAssertionAction

-- This regression checks execution traces; defer the symbolic assertion checks.
set_option veil.deferVCGeneration true

individual flag : Bool
individual phase : Nat
individual selected : Nat

#gen_state

procedure choose_flag {
  let choice ← pick Bool
  return choice
}

after_init {
  flag ← choose_flag
  require flag
  phase := 0
  selected := 0
}

action prepare {
  require phase = 0
  let n ← pick (Fin 3)
  if n.val = 2 then
    flag ← choose_flag
  else
    flag := true
  selected := n.val
  phase := 1
}

action check {
  require phase = 1
  let inspect ← choose_flag
  if inspect then
    if flag ∧ selected = 2 then
      assert flag
      let extra ← pick (Fin 2)
      selected := selected + extra.val
      assert selected < 3
      -- Neither this pick nor the final phase update runs on the failing route.
      flag ← choose_flag
    else
      selected := 0
  else
    selected := 1
  phase := 2
}

invariant true

#guard_msgs in
#gen_spec

/--
error: ❌ Violation: assertion_failure
  State 0 (via init):
    choices: choice = true
    flag = true
    phase = 0
    selected = 0
  State 1 (via prepare):
    choices: n = 2, choice = true
    flag = true
    phase = 1
    selected = 2
  State 2 (via check):
    choices: choice = true, extra = 1
    flag = true
    phase = 1
    selected = 3
-/
#guard_msgs in
#model_check interpreted {} {}

/--
error: ❌ Violation: assertion_failure
  State 0 (via init):
    choices: choice = true
    flag = true
    phase = 0
    selected = 0
  State 1 (via prepare):
    choices: n = 2, choice = true
    flag = true
    phase = 1
    selected = 2
  State 2 (via check):
    choices: choice = true, extra = 1
    flag = true
    phase = 1
    selected = 3
-/
#guard_msgs in
#model_check interpreted {} {} (sequential := true)

end TraceChoicesAssertionAction

/-!
Here the assertion fails inside a procedure called from an `if` condition. Both the callee and its
own callee mutate state, and the failing step must show their picks and the state at the assertion,
before the caller's branches run. Only `base = delta = 2` and `audit = 1` can fail; `delta = 2`
requires the inner Boolean choice to be true. The initializer and `arm` have no picks.
-/

veil module TraceChoicesAssertionProcedure

set_option veil.deferVCGeneration true

individual phase : Nat
individual value : Nat

#gen_state

after_init {
  phase := 0
  value := 0
}

procedure choose_delta {
  let n ← pick (Fin 3)
  if n.val = 2 then
    let high ← pick Bool
    if high then
      value := 2
      return 2
    else
      value := 1
      return 1
  else
    value := n.val
    return n.val
}

procedure validate (base : Nat) {
  let delta ← choose_delta
  let audit : Fin 2 :| audit.val = 1
  value := base + delta + audit.val
  assert value < 5
  let reset ← pick Bool
  if reset then
    value := 0
  else
    value := 1
  return value
}

action arm {
  require phase = 0
  phase := 1
}

action run {
  require phase = 1
  let base ← pick (Fin 3)
  if base.val = 2 then
    if (← validate base.val) = 0 then
      phase := 2
    else
      phase := 3
  else
    value := base.val
    phase := 2
}

invariant true

#guard_msgs in
#gen_spec

/--
error: ❌ Violation: assertion_failure
  State 0 (via init):
    phase = 0
    value = 0
  State 1 (via arm):
    phase = 1
    value = 0
  State 2 (via run):
    choices: base = 2, n = 2, high = true, audit = 1
    phase = 1
    value = 5
-/
#guard_msgs in
#model_check interpreted {} {}

/--
error: ❌ Violation: assertion_failure
  State 0 (via init):
    phase = 0
    value = 0
  State 1 (via arm):
    phase = 1
    value = 0
  State 2 (via run):
    choices: base = 2, n = 2, high = true, audit = 1
    phase = 1
    value = 5
-/
#guard_msgs in
#model_check interpreted {} {} (sequential := true)

end TraceChoicesAssertionProcedure

/-!
Only `lock` picking `1, true, 2` reaches a nonterminating state without successors. Other branches
can run `release` and terminate normally. `release` picks before checking its guard, but these
discarded executions must not add choices or an extra state to the deadlock trace.
-/

veil module TraceChoicesDeadlockAfterSteps

individual code : Nat
individual phase : Nat
individual ready : Bool

#gen_state

after_init {
  ready := *
  require ready
  code := 0
  phase := 0
}

procedure choose_code {
  let high ← pick Bool
  if high then
    let n ← pick (Fin 3)
    if n.val = 2 then
      ready := false
    else
      ready := true
    return n.val
  else
    let n ← pick (Fin 2)
    ready := true
    return n.val
}

action arm {
  require phase = 0
  phase := 1
}

action lock {
  require phase = 1
  let offset ← pick (Fin 2)
  code ← choose_code
  if ready then
    code := code + offset.val
  else
    if offset.val = 1 then
      code := code + offset.val
    else
      ready := true
  phase := 2
}

action release {
  let probe ← pick Bool
  require phase = 2 ∧ ready
  if probe then
    let n ← pick (Fin 2)
    code := n.val
  else
    code := 0
  phase := 3
}

invariant true
termination phase = 3

#gen_spec

/--
error: ❌ Violation: deadlock
  State 0 (via init):
    choices: ready = true
    code = 0
    phase = 0
    ready = true
  State 1 (via arm):
    code = 0
    phase = 1
    ready = true
  State 2 (via lock):
    choices: offset = 1, high = true, n = 2
    code = 3
    phase = 2
    ready = false
-/
#guard_msgs in
#model_check interpreted {} {}

/--
error: ❌ Violation: deadlock
  State 0 (via init):
    choices: ready = true
    code = 0
    phase = 0
    ready = true
  State 1 (via arm):
    code = 0
    phase = 1
    ready = true
  State 2 (via lock):
    choices: offset = 1, high = true, n = 2
    code = 3
    phase = 2
    ready = false
-/
#guard_msgs in
#model_check interpreted {} {} (sequential := true)

end TraceChoicesDeadlockAfterSteps

/-!
A deadlock can also be one of several initial states. Its only choices are those of the initializer,
including its nested procedures. All other initial states keep `pulse` enabled indefinitely. Picks
in the disabled `pulse` must not be confused with the initializer's choices.
-/

veil module TraceChoicesDeadlockInitial

individual enabled : Bool
individual ticket : Nat

#gen_state

procedure choose_flag {
  let flag ← pick Bool
  return flag
}

procedure choose_ticket {
  if (← choose_flag) then
    let n ← pick (Fin 3)
    if n.val = 2 then
      enabled := false
    else
      enabled := true
    return n.val
  else
    let n : Fin 2 :| n.val = 1
    enabled := true
    return n.val
}

after_init {
  ticket ← choose_ticket
}

action pulse {
  let probe ← choose_flag
  require enabled
  if probe then
    ticket := 0
  else
    ticket := 1
}

invariant true
termination false = true

#gen_spec

/--
error: ❌ Violation: deadlock
  State 0 (via init):
    choices: flag = true, n = 2
    enabled = false
    ticket = 2
-/
#guard_msgs in
#model_check interpreted {} {}

/--
error: ❌ Violation: deadlock
  State 0 (via init):
    choices: flag = true, n = 2
    enabled = false
    ticket = 2
-/
#guard_msgs in
#model_check interpreted {} {} (sequential := true)

end TraceChoicesDeadlockInitial
