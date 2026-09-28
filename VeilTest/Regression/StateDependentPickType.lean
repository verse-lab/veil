module

public import Veil

/-!
# Regression: `pick` types that mention mutable state

In `let x ← rhs`, the type of `x` is elaborated under the state opening of the
`let` statement. The right-hand side used to be elaborated under a second,
inner opening, so a type mentioning mutable state (such as `{ i // i ∈ s }`)
referred to field views out of scope of `x`, and using `x.val` failed with
"Type of `x` is not known".

`pick_after_call` checks that the right-hand side still observes the state
written by a call lifted out of the statement: after `clear_and_return n`
empties `s`, the only candidate is `n`.
-/

veil module StateDependentPickType

type node
type NodeSet
instantiate nset : TSet node NodeSet

individual s : NodeSet
individual last : Option node
individual lastPair : Option (node × node)
individual picked : Option node
individual expected : Option node

#gen_state

after_init {
  s := nset.empty
  last := none
  lastPair := none
  picked := none
  expected := none
}

action add (n : node) {
  s := nset.insert n s
}

#guard_msgs in
action pick_member {
  let i ← pick { i // i ∈ s }
  last := some i.val
}

#guard_msgs in
action pick_member_such_that (n : node) {
  let m : { m // m ∈ s } :| m.val ≠ n
  last := some m.val
}

#guard_msgs in
action pick_pair {
  let (i, j) ← pick ({ i // i ∈ s } × { j // j ∈ s })
  lastPair := some (i.val, j.val)
}

-- Here and in `pick_after_call`, the dropped warnings say `wp_local_eq` cannot
-- be generated for these binders whose type mentions state; that also happens
-- with the type written on the binder, independently of this regression, and
-- model checking is unaffected.
#guard_msgs(drop warning) in
action pick_opt {
  let some i ← pick (Option { i // i ∈ s })
    | last := none
  last := some i.val
}

procedure clear_and_return (n : node) {
  s := nset.empty
  return n
}

#guard_msgs(drop warning) in
action pick_after_call (n : node) {
  let i ← pick { i // i ∈ nset.insert (← clear_and_return n) s }
  picked := some i.val
  expected := some n
  last := none
  lastPair := none
}

invariant [last_in_s] ∀ n, last = some n → n ∈ s
invariant [pair_in_s] ∀ a b, lastPair = some (a, b) → a ∈ s ∧ b ∈ s
invariant [picked_after_call] picked = expected

#guard_msgs(drop warning) in
#gen_spec

/-- info: ✅ No violation (explored 72 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 2, NodeSet := OrdList (Fin 2) } {}

end StateDependentPickType
