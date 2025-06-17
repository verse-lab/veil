import Veil

veil module NonDetStateTest

type address

relation initial_msg (originator : address) (dst : address) (r : address) (v : address)
individual x : Bool

#gen_state

after_init {
  initial_msg O D R V := False
  x := False
}

action nondet = {
  let st' ← pick σ
  set st'
}

action noop (n : address) = {
  pure ()
}
invariant True

#gen_spec

/--
info: Initialization must establish the invariant:
  inv_0 ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  nondet
    termination ... ✅
    inv_0 ... ✅
  noop
    termination ... ✅
    inv_0 ... ✅
-/
#guard_msgs in
#check_invariants

end NonDetStateTest
