import Veil.DSL
import Test.TestUtil


set_option linter.unusedVariables false

veil module InnerChild
type node

immutable individual n : node

#gen_state

after_init { pure () }

#guard_msgs(drop warning) in
#gen_spec

end InnerChild

veil module Child
type block
type node
type queue

individual x : Prop

immutable individual b : block
relation r : block -> block -> Prop
relation n_have_privilege : node → Prop

includes InnerChild node _ _ as ic

#gen_state

after_init {
  pure ()
}

-- assumption ∃ b, r b b

#guard_msgs(drop warning) in
#gen_spec

end Child

veil module Parent
type block
type node
type queue

includes Child block _ _ node _ _ queue _ _

#gen_state

after_init {
  pure ()
}

/--
error: Error in action Parent.try_modify_b: individual b in module Child was declared immutable, but trying to assign to it!
-/
#guard_msgs in
action try_modify_b (new_block : block) = {
  Child.b := new_block
}

/--
error: Error in action Parent.try_modify_inner_child: individual n in module InnerChild was declared immutable, but trying to assign to it!
-/
#guard_msgs in
action try_modify_inner_child (new_node : node) = {
  Child.ic.n := new_node
}

-- FIXME: cannot refer to included state components in properties
-- assumption ∃ b, Child.r b b

#guard_msgs(drop warning) in
#gen_spec

end Parent
