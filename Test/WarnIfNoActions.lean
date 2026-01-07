import Veil

veil module Test

individual x : Bool

#gen_state

after_init { pure () }

invariant true

/-- warning: you have not defined any actions for this specification; did you forget? -/
#guard_msgs in
#gen_spec
