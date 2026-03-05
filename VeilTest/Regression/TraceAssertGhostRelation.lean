import Veil

/-! Ghost relations used in `sat trace` assertions should elaborate correctly. -/

veil module TraceAssertGhostRelation

type node

function crashed (n : node) : Bool
ghost relation alive (n : node) := ¬ crashed n

after_init {
  crashed N := false
}

action doCrash (n : node) {
  require alive n
  crashed n := true
}

action do_nothing {
  pure ()
}

#guard_msgs(drop warning) in
#gen_spec

#guard_msgs(drop info) in
sat trace {
  any action
  assert (∃ n, ¬alive n)
}

end TraceAssertGhostRelation
