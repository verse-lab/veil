import Veil

veil module TraceWithNoActions

type node
type value

immutable individual v₀ : value
relation W (n : node) (v : value) : Bool

after_init {
  W N V := V == v₀
}

#guard_msgs(drop warning) in
#gen_spec

-- We are testing that there is no error here
#guard_msgs(drop info) in
sat trace {}

end TraceWithNoActions
