import Veil.DSL
import Test.TestUtil



veil module TestNoState

individual x : Prop

/-- error: State has not been declared so far: run `#gen_state` -/
#guard_msgs in
after_init { pure () }

/-- error: State has not been declared so far: run `#gen_state` -/
#guard_msgs in
action foo = { pure () }

/-- error: State has not been declared so far: run `#gen_state` -/
#guard_msgs in
invariant [inv] True

/-- error: State has not been declared so far: run `#gen_state` -/
#guard_msgs in
#gen_spec

/-- error: State has not been declared so far: run `#gen_state` -/
#guard_msgs in
#check_invariants

/-- error: State has not been declared so far: run `#gen_state` -/
#guard_msgs in
#check_invariants?

/-- error: State has not been declared so far: run `#gen_state` -/
#guard_msgs in
#check_invariant inv

/-- error: State has not been declared so far: run `#gen_state` -/
#guard_msgs in
#check_action foo

/-- error: State has not been declared so far: run `#gen_state` -/
#guard_msgs in
sat trace { } by { bmc_sat }

/-- error: State has not been declared so far: run `#gen_state` -/
#guard_msgs in
unsat trace { } by { bmc }

end TestNoState

veil module TestNoInit


individual x : Prop

#gen_state

/--
error: You have not defined any initial state for this specification: write an `after_init` declaration
-/
#guard_msgs in
#gen_spec


end TestNoInit

veil module TestNoGenSpec

individual x : Prop

#gen_state

after_init { x := True }

action foo = { pure () }

invariant [inv] x

/-- error: The specification for module TestNoGenSpec has not been defined: run `#gen_spec` -/
#guard_msgs in
#check_invariants

end TestNoGenSpec


veil module TestStateAfterGenState

individual x : Prop

#gen_state

/--
error: You have already run #gen_state for module TestStateAfterGenState: adding state components is no longer allowed!
-/
#guard_msgs in
relation foo (n : Prop)

end TestStateAfterGenState


veil module TestInvariantAfterGenSpec

individual x : Prop

#gen_state

after_init { x := True }

action foo = { pure () }

invariant [inv] x

#gen_spec

/--
error: You have already run #gen_spec for module TestInvariantAfterGenSpec: adding actions or invariants is no longer allowed!
-/
#guard_msgs in
safety True

/--
error: You have already run #gen_spec for module TestInvariantAfterGenSpec: adding actions or invariants is no longer allowed!
-/
#guard_msgs in
action bar = { pure () }

end TestInvariantAfterGenSpec
