import Veil.DSL
import Veil.TestUtil

section Test

individual x : Prop

#gen_state Test

after_init { }

invariant True

/-- warning: you have not defined any actions for this specification; did you forget? -/
#guard_msgs in
#gen_spec Test
