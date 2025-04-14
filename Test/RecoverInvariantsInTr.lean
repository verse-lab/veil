import Veil
import Veil.DSL.Check.InvariantManipulation

set_option veil.gen_sound true
set_option synthInstance.maxSize 1000000

veil module Ring

type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node -> Prop
relation pending : node -> node -> Prop

#gen_state

after_init {
  leader N := False
  pending M N := False
}

action send = {
  let n : node ← fresh
  let next : node ← fresh
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := True
}

action recv = {
  let sender : node ← fresh
  let n : node ← fresh
  let next : node ← fresh
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  -- message may or may not be removed
  -- this models that multiple messages might be in flight
  pending sender n := *
  if (sender = n) then
    leader n := True
  else
    -- pass message to next node
    if (le n sender) then
      pending sender next := True
}

safety [single_leader] leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#gen_spec

#guard_msgs(drop info, drop warning) in
#check_invariants

#recover_invariants_in_tr

prove_inv_inductive by {
  constructor
  . intro st has hinit
    sdestruct_goal <;> already_proven_init
  · intro st st' has hinv hnext
    sts_induction <;> sdestruct_goal <;> already_proven_next_tr
}

#split_invariants

end Ring
