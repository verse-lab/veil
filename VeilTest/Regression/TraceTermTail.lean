import Veil

-- The trace command's optional proof term must start on the same line as the
-- closing brace. Previously the parser greedily tried to consume whatever
-- followed the trace command as its proof term: a subsequent
-- `set_option ... in <command>` parsed as a term up to `in` and then failed
-- ("unexpected token ...; expected spec"), taking the whole trace command down
-- with it; error recovery then ran the inner command without the option.

veil module TraceTermTail

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action set_flag {
  flag := true
}

invariant [flag_unset] ¬ flag

#gen_spec

#guard_msgs(drop warning, drop info) in
sat trace [first] {
  set_flag
}

#guard_msgs(drop warning, drop info) in
set_option veil.violationIsError false in
sat trace [second] {
  set_flag
  set_flag
}

end TraceTermTail
