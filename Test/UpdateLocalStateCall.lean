import Veil

veil module Test
type node

individual x : Bool

#gen_state

after_init {
  x := False
}

procedure setTrue = {
  x := True
}

action thisshouldntfail = {
  setTrue
  assert x
}

action thisshouldntfail_2 = {
  let _f ← setTrue
  assert x
}

action becauseitshouldmeanthesameasthis = {
  x := True
  assert x
}

#guard_msgs(drop warning) in
#gen_spec

-- NOTE: We are doing something dodgy (but INTENTIONAL) here!
-- In defining the `invariant` after `#gen_spec`, we ensure that `inv` is
-- `True`, but this clause is checked nonetheless, i.e. it is not assumed
-- in the pre-state, but IS checked in the post-state.
-- invariant [x_is_true] x
@[invDef, invSimp] def x_is_true : {node : Type} → [DecidableEq node] → [Nonempty node] → (State node) → Prop :=
fun {node} [DecidableEq node] [Nonempty node] st => State.casesOn st fun x => x = true

/--
info: The following set of actions must preserve the invariant:
  thisshouldntfail
    x_is_true ... ✅
-/
#guard_msgs in
#check_action thisshouldntfail

/--
info: The following set of actions must preserve the invariant:
  thisshouldntfail_2
    x_is_true ... ✅
-/
#guard_msgs in
#check_action thisshouldntfail_2

/--
info: The following set of actions must preserve the invariant:
  becauseitshouldmeanthesameasthis
    x_is_true ... ✅
-/
#guard_msgs in
#check_action becauseitshouldmeanthesameasthis
end Test
