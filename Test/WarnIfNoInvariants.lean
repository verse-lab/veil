import Veil.DSL
import Veil.TestUtil

namespace Test

individual x : Prop

#gen_state

after_init { pure () }
action foo = { pure () }

/-- warning: you have not defined any invariants for this specification; did you forget? -/
#guard_msgs in
#gen_spec
