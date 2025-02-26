import Veil.DSL
import Test.TestUtil

veil module Test

individual x : Prop

#gen_state

after_init { pure () }

invariant True

/-- warning: you have not defined any actions for this specification; did you forget? -/
#guard_msgs in
#gen_spec
