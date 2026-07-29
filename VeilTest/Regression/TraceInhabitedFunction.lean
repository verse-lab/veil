import Veil

veil module ErrorRelatedToInhabitedInTraceFunction

type node
function crashedInRound (n : node) : Nat

after_init {
  pure ()
}

#guard_msgs(drop warning) in
#gen_spec

#guard_msgs(drop info) in
sat trace {}

end ErrorRelatedToInhabitedInTraceFunction


veil module AnotherErrorRelatedToInhabitedInTraceFunction

type node
type value
function crashedInRound (n : node) : value

after_init {
  pure ()
}

#guard_msgs(drop warning) in
#gen_spec

#guard_msgs(drop info) in
sat trace {}

end AnotherErrorRelatedToInhabitedInTraceFunction
