import Veil
set_option veil.experimental.bmcCache true
veil module CacheNamesProbe
type pre
type post
type tag
individual flag : Bool
#gen_state
after_init { flag := false }
action enable { flag := true }
action disable { flag := false }
invariant True
#gen_spec
end CacheNamesProbe
