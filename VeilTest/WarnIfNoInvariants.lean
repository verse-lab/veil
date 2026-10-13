module

public import Veil

veil module Test

individual x : Bool

#gen_state

after_init { pure () }
action foo { pure () }

/-- warning: you have not defined any invariants or temporal properties for this specification; did you forget? -/
#guard_msgs in
#gen_spec

end Test

-- No warning when the specification declares a temporal property.
veil module TestLiveness

individual x : Bool

#gen_state

after_init { pure () }
action foo { pure () }

liveness [eventually_x] ◇ ⌜ x = true ⌝

#guard_msgs in
#gen_spec

end TestLiveness
