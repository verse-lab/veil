import Veil
veil module Semantics
individual flag : Prop

#gen_state

after_init {
  flag := False
}

action nondet (fail : Prop) = {
  if fail then
    flag := True
  else
    flag := False
}

action nondet_fresh = {
  let fail ← fresh Prop
  if fail then
    flag := True
  else
    flag := False
}

#print nondet.tr
#print nondet_fresh.tr


action fail_nondet (fail : Prop) = {
  if fail then
    assert False
    flag := True
  else
    flag := False
}

action fail_nondet_fresh = {
  let fail ← fresh Prop
  if fail then
    assert False
    flag := True
  else
    flag := False
}

/-
transition fail_nondet_fresh2

(∃ fail, if fail then False else flag' = False)

-/

#print fail_nondet.tr
#print fail_nondet_fresh.tr

invariant True

#gen_spec

unsat trace {
  fail_nondet_fresh
} by bmc

def fail_nondet_fresh' := conv! (unfold Wp.toWlp fail_nondet_fresh; simp) => Wp.toWlp fail_nondet_fresh
#print fail_nondet_fresh
#print fail_nondet_fresh'
#print fail_nondet_fresh.tr

def fail_nondet' (fail : Prop):= conv! (unfold Wp.toWlp fail_nondet; simp) => Wp.toWlp (fail_nondet fail)
#print fail_nondet
#print fail_nondet'

#print nondet.genE
#print nondet_fresh

#print fail_nondet
#print fail_nondet_fresh


end Semantics
