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

/-- info: false -/
#guard_msgs in
#eval hasStateHOExist (Lean.mkConst `empty.tr.raw)


action call_empty = {
  call !empty
}

/-- info: true -/
#guard_msgs in
#eval hasStateHOExist (Lean.mkConst `call_empty.tr.raw)

-- #print call_empty.tr.raw
-- ∃ s' ret, s' = st ∧ st' = s'
-- #check exists_const #check exists_eq_left
-- In this case, `exists_const` gets rid of `∃ ret`, which enables `exists_eq_left`.
attribute [quantifierElim] exists_const exists_eq_left

def call_empty := conv! (unfold call_empty.tr.raw; simp only [quantifierElim]) => call_empty.tr.raw
/-- info: false -/
#guard_msgs in
#eval hasStateHOExist (Lean.mkConst `call_empty)

action retval = {
  return 42
}

action call_retval = {
  call !retval
}

-- #print call_retval.tr.raw
-- ∃ s' ret, (s' = st ∧ ret = 42) ∧ st' = s'
-- #check and_assoc
attribute [quantifierElim high] and_assoc elim_exists_State
def call_retval := conv! (unfold call_retval.tr.raw; simp only [quantifierElim]) => call_retval.tr.raw
/-- info: false -/
#guard_msgs in
#eval hasStateHOExist (Lean.mkConst `_call_retval)

action with_if = {
  if (x) {
    r N M := False
  }
}

action call_with_if = {
  call !with_if
  x := False
}


-- #print call_with_if.tr.raw
--  ∃ s', (if st.x then s' = { r := fun N M => False, x := st.x } else s' = st) ∧ st' = { r := s'.r, x := False }
-- #check ite_push_down_eq
attribute [quantifierElim] ite_push_down_eq
def call_with_if := conv! (unfold call_with_if.tr.raw; simp? only [quantifierElim]) => call_with_if.tr.raw
/-- info: false -/
#guard_msgs in
#eval hasStateHOExist (Lean.mkConst `call_with_if)

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

-- #print call_with_if_fresh.tr
-- ∃ s',
--   (if st.x then ∃ t, s' = { r := fun N x => ¬x = t ∧ st.r N x, x := st.x } else s' = st) ∧
--     st' = { r := s'.r, x := False };
-- #check exists_and_right' #check exists_and_left'
attribute [quantifierElim] exists_and_right' exists_and_left' ite_exists_push_out

def call_with_if_fresh := conv! (unfold call_with_if_fresh.tr.raw; simp? only [quantifierElim]) => call_with_if_fresh.tr.raw
/-- info: false -/
#guard_msgs in
#eval hasStateHOExist (Lean.mkConst `call_with_if_fresh)


action with_if_fresh_more = {
  if (x) {
    fresh m : node in
    r N m := False
    require x
  } else {
    skip
  }
}

#print with_if_fresh_more.tr

action call_with_if_fresh_more = {
  call !with_if_fresh_more
  x := False
}

-- #print call_with_if_fresh_more.tr.raw
-- ∃ s',
--   (if st.x then ∃ t, s' = { r := fun N x => ¬x = t ∧ st.r N x, x := st.x } ∧ st.x else s' = st) ∧
--     st' = { r := s'.r, x := False }
attribute [quantifierElim] ite_push_down_eq ite_push_down_eq_and_both ite_push_down_eq_and_left ite_push_down_eq_and_right

def call_with_if_fresh_more := conv! (unfold call_with_if_fresh_more.tr.raw; simp? only [quantifierElim]) => call_with_if_fresh_more.tr.raw
/-- info: false -/
#guard_msgs in
#eval hasStateHOExist (Lean.mkConst `call_with_if_fresh_more)


end Test
