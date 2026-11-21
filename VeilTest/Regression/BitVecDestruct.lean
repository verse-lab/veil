module

public import Veil

veil module BitVecActionParameters

relation foo : BitVec 1 → BitVec 1 → Bool
#gen_state

after_init { foo R C := false }

action set (r c : BitVec 1) {
  require r ≠ c
  foo r c := true
}

invariant [irrefl] ¬ foo X X

#gen_spec
#check_invariants

end BitVecActionParameters

veil module BitVecStateField

individual word : BitVec 8
#gen_state

after_init { word := 1#8 }

action set (v : BitVec 8) {
  require v ≠ 0#8
  word := v
}

transition keep { word' = word }

invariant [nonzero] word ≠ 0#8

#gen_spec
#check_invariants

sat trace {
  set
  assert (word = 2#8)
}

end BitVecStateField
