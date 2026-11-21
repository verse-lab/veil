module

public import Veil

/-! Regression for #182. Opening 64 fields for each of 64 assignments produces
long runs of unused field views. Cleanup must handle them at the default
recursion limit and retain the field read by the final assignment. -/

veil module WideInitializer

individual b0 : Bool
individual b1 : Bool
individual b2 : Bool
individual b3 : Bool
individual b4 : Bool
individual b5 : Bool
individual b6 : Bool
individual b7 : Bool
individual b8 : Bool
individual b9 : Bool
individual b10 : Bool
individual b11 : Bool
individual b12 : Bool
individual b13 : Bool
individual b14 : Bool
individual b15 : Bool
individual b16 : Bool
individual b17 : Bool
individual b18 : Bool
individual b19 : Bool
individual b20 : Bool
individual b21 : Bool
individual b22 : Bool
individual b23 : Bool
individual b24 : Bool
individual b25 : Bool
individual b26 : Bool
individual b27 : Bool
individual b28 : Bool
individual b29 : Bool
individual b30 : Bool
individual b31 : Bool
individual b32 : Bool
individual b33 : Bool
individual b34 : Bool
individual b35 : Bool
individual b36 : Bool
individual b37 : Bool
individual b38 : Bool
individual b39 : Bool
individual b40 : Bool
individual b41 : Bool
individual b42 : Bool
individual b43 : Bool
individual b44 : Bool
individual b45 : Bool
individual b46 : Bool
individual b47 : Bool
individual b48 : Bool
individual b49 : Bool
individual b50 : Bool
individual b51 : Bool
individual b52 : Bool
individual b53 : Bool
individual b54 : Bool
individual b55 : Bool
individual b56 : Bool
individual b57 : Bool
individual b58 : Bool
individual b59 : Bool
individual b60 : Bool
individual b61 : Bool
individual b62 : Bool
individual b63 : Bool

#gen_state

after_init {
  b0 := true
  b1 := false
  b2 := false
  b3 := false
  b4 := false
  b5 := false
  b6 := false
  b7 := false
  b8 := false
  b9 := false
  b10 := false
  b11 := false
  b12 := false
  b13 := false
  b14 := false
  b15 := false
  b16 := false
  b17 := false
  b18 := false
  b19 := false
  b20 := false
  b21 := false
  b22 := false
  b23 := false
  b24 := false
  b25 := false
  b26 := false
  b27 := false
  b28 := false
  b29 := false
  b30 := false
  b31 := false
  b32 := false
  b33 := false
  b34 := false
  b35 := false
  b36 := false
  b37 := false
  b38 := false
  b39 := false
  b40 := false
  b41 := false
  b42 := false
  b43 := false
  b44 := false
  b45 := false
  b46 := false
  b47 := false
  b48 := false
  b49 := false
  b50 := false
  b51 := false
  b52 := false
  b53 := false
  b54 := false
  b55 := false
  b56 := false
  b57 := false
  b58 := false
  b59 := false
  b60 := false
  b61 := false
  b62 := false
  b63 := b0
}

action step { b0 := false }

invariant [lastField] b63

#gen_spec

#guard_msgs (drop info) in
sat trace [copySurvives] {
  step
  assert (!b0 && b63)
}

end WideInitializer
