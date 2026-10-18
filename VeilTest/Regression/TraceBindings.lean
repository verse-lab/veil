module

public import Veil

/-! Symbolic trace parameters name one existential witness throughout a query.
Action holes and omitted arguments instead choose a fresh witness at each call. -/

veil module TraceBindings

type node

relation visited : node → Bool
function next : node → node

#gen_state

after_init {
  visited N := false
  next N := N
}

action visit (n : node) {
  require ¬ visited n
  visited n := true
}

action visit_and_retarget (n target : node) {
  require ¬ visited n
  visited n := true
  next N := target
}

invariant True

#gen_spec

-- A named witness persists across calls. The second visit is disabled.
#guard_msgs(drop info, drop warning) in
unsat trace [same_node_twice] (n : node) {
  visit n
  visit n
}

-- Omitted parameters and explicit holes are fresh at each occurrence.
#guard_msgs(drop info, drop warning) in
sat trace {
  visit
  visit
}

#guard_msgs(drop info, drop warning) in
sat trace {
  visit _
  visit _
}

-- Multiple binders in a group are available in both calls and assertions.
#guard_msgs(drop info, drop warning) in
sat trace [different_nodes] (n m : node) {
  assert (n ≠ m)
  visit n
  visit m
  assert (visited n ∧ visited m)
}

-- Different names do not imply different values.
#guard_msgs(drop info, drop warning) in
sat trace (n : node) (m : node) {
  assert (n = m)
  visit n
  assert (visited m)
}

-- Assertions add constraints to the query, including to earlier choices.
#guard_msgs(drop info, drop warning) in
unsat trace (n m : node) {
  visit n
  visit m
  assert (n = m)
}

-- A quantifier inside an assertion has its usual local scope. Its `n` is
-- independent of the header witness, which remains available afterwards.
#guard_msgs(drop info, drop warning) in
sat trace (n : node) {
  visit n
  assert (∃ n, ¬ visited n)
  assert (visited n)
}

-- A compound action argument reads the state before this action. The same
-- action changes the field, so reading its post-state would visit `m` instead.
#guard_msgs(drop info, drop warning) in
sat trace (n m : node) {
  assert (n ≠ m)
  visit_and_retarget (next n) m
  assert (visited n ∧ ¬ visited m ∧ next n = m)
}

-- State expressions are reevaluated at each call, rather than at query entry.
#guard_msgs(drop info, drop warning) in
sat trace (n m : node) {
  assert (n ≠ m)
  visit_and_retarget n m
  visit (next n)
  assert (visited n ∧ visited m)
}

-- Explicit arguments and holes may be mixed. A later assertion constrains
-- the fresh target without rebinding the explicit argument.
#guard_msgs(drop info, drop warning) in
sat trace (n m : node) {
  assert (n ≠ m)
  visit_and_retarget n _
  assert (visited n ∧ ¬ visited m ∧ next n = m)
}

-- Header witnesses work even when there are no transitions.
#guard_msgs(drop info, drop warning) in
sat trace (n : node) {
  assert (¬ visited n)
}

-- Uppercase header names remain shared witnesses inside assertions instead of
-- being implicitly universally quantified by the assertion elaborator.
#guard_msgs(drop info, drop warning) in
sat trace (N : node) {
  visit N
  assert (visited N)
  assert (∃ m, m ≠ N ∧ ¬ visited m)
}

-- An unused witness may be omitted by the solver, but must not prevent trace
-- reconstruction or invent a value for it.
#guard_msgs(drop info, drop warning) in
sat trace (unused : node) {
  visit
}

-- An empty binding type makes the entire query unsatisfiable, even when
-- simplification proves this before the SMT solver produces a result.
#guard_msgs(drop info, drop warning) in
unsat trace (impossible : False) {}

/-- error: No satisfying trace exists -/
#guard_msgs(error, drop info, drop warning) in
sat trace (impossible : False) {}

end TraceBindings

-- Named witnesses also work in modules with no actions and zero-step queries.
veil module TraceBindingsWithoutActions

type node
relation visited : node → Bool

#gen_state

after_init {
  visited N := false
}

#guard_msgs(drop warning) in
#gen_spec

#guard_msgs(drop info, drop warning) in
sat trace (n : node) {
  assert (¬ visited n)
}

end TraceBindingsWithoutActions
