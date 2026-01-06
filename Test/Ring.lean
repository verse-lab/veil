import Veil

set_option linter.unusedVariables false

veil module Ring

type node

instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

action send (n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := true
}

action recv (sender n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  pending sender n := false
  if (sender = n) then
    leader n := true
  else
    if (le n sender) then
      pending sender next := true
}

safety [single_leader] leader N ∧ leader M → N = M
invariant [leader_greatest] leader L → le N L
invariant [inv_1] pending S D ∧ btw S N D → le N S
invariant [inv_2] pending L L → le N L

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  single_leader ... ✅
  leader_greatest ... ✅
  inv_1 ... ✅
  inv_2 ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  recv
    doesNotThrow ... ✅
    single_leader ... ✅
    leader_greatest ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
  send
    doesNotThrow ... ✅
    single_leader ... ✅
    leader_greatest ... ✅
    inv_1 ... ✅
    inv_2 ... ✅
-/
#guard_msgs in
#check_invariants

/-- info: ✅ No violation (explored 1024 states) -/
#guard_msgs in
#model_check { node := Fin 5 } { }

/--
info: ✅ Satisfying trace found
  Instantiation:
    node = Fin 2
  State 0 (via init):
    leader = []
    pending = []
  State 1 (via send(n=0, next=1)):
    leader = []
    pending = [[0, 1]]
  State 2 (via send(n=0, next=1)):
    leader = []
    pending = [[0, 1]]
  State 3 (via recv(n=1, next=0, sender=0)):
    leader = []
    pending = [[0, 0]]
-/
#guard_msgs in
sat trace {
  send
  send
  recv
}

#guard_msgs in
unsat trace {
  any 4 actions
  assert (∃ n₁ n₂, n₁ ≠ n₂ ∧ leader n₁ ∧ leader n₂)
}

end Ring
