import Veil.DSL

open Classical

section Test

type node

relation r (n : node) (m : node)
individual x : Prop

#gen_state Test

after_init {
  r N N := False
  x := False
}

action empty = {
  skip
}


#print empty.tr.raw

-- set_option trace.debug true

action call_empty = {
  call !empty
}

#print call_empty.tr.raw


action retval = {
  return 42
}

action call_retval = {
  call !retval
}

#print call_retval.tr.raw


action with_if = {
  if (x) {
    r N M := False
  }
}

action call_with_if = {
  call !with_if
  x := False
}

action with_if_fresh = {
  if (x) {
    fresh m : node in
    r N m := False
  }
}

action call_with_if_fresh = {
  call !with_if_fresh
  x := False
}

action with_if_fresh_more = {
  if (x) {
    fresh m : node in
    r N m := False
    require x
  } else {
    skip
  }
}

action call_with_if_fresh_more = {
  call !with_if_fresh_more
  x := False
}

action nested_call = {
  call !call_with_if_fresh_more
  x := False
}

#print nested_call.tr.raw

action callee_with_if_some = {
  if m where (r m m) {
    if n where (r n n ∧ n ≠ m) {
      r n m := True
      require x
      x := False
    }
  }
}

action with_if_some_nested = {
  if m where (r m m) {
    if n where (r n n ∧ n ≠ m) {
      r n m := True
      require x
      x := False
      call !callee_with_if_some
    }
  }
}


#print with_if_some_nested.tr.raw
def with_if_some_nested := conv! (unfold with_if_some_nested.tr.raw; simp? only [smtSimp, logicSimp, and_assoc]; simp? only [quantifierElim]) => with_if_some_nested.tr.raw
#print with_if_some_nested

-- FIXME: I think we need a `simproc` version of `forall_and_left` and `forall_and_right`, specialised for `State`
-- variable [ne_axiom : Nonempty (Test.State node)]
-- def test := conv! (unfold with_if_some_nested; rw [@forall_and_left (Test.State node) ne_axiom]) => with_if_some_nested

-- #eval hasStateHOInnerForall (Lean.mkConst `with_if_some_nested)


action nondet_assgn_modify = {
  x := *
  x := False
}

action clobber = {
  x := *
  r N M := *
}

#print clobber.tr.raw

end Test
