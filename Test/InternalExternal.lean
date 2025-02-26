import Veil.DSL
import Test.TestUtil

veil module Test


individual x : Prop

#gen_state

action req = {
  require False
}

example : forall s s' (Q : Prop), req.tr s s' -> Q := by simp [actSimp]
example : forall s Q, ¬ req s Q := by simp [actSimp]
