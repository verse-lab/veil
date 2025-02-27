import Veil.DSL
import Test.TestUtil
import Veil.Std

veil module Test₁


type node

relation r (n : node) (m : node) : Prop
relation r' (n : Nat) (m : node) : Prop
individual nd : node

#gen_state

after_init {
  r N M := False
  r' N M := False
}

action f (n : Nat)  = {
  pure n
}

action foo (x : node) = {
  pure ()
}

action fresh_node (yy : node) = {
  let n <- fresh node
  nd := n
}


#guard_msgs(drop warning) in
#gen_spec

end Test₁

veil module Test₂


type node'
type node''

relation r'' (n : node') (m : node') : Prop
includes Test₁ node' node'_dec node'_ne as test
includes Test₁ node' _ _ as test'

#gen_state

after_init {
  r'' N M := False
}

action g = {
  let n <- fresh node'
  test.r' N n := True
  r'' := test.r
  r'' := test'.r
  let _ <- test.f 1
  test'.f 1
}

invariant True

#gen_spec
