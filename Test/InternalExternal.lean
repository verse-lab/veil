import Veil.DSL
import Test.TestUtil

veil module Test


individual x : Prop

#gen_state

action req = {
  require False
}


example : forall (r : ρ) (s s' : σ) (Q : Prop), req.ext.tr r s s' -> Q := by simp [actSimp]
example : forall (r : ρ) (s : σ) (Q), ¬ req.wpGen (fun _ => False) Q r s := by simp [actSimp]
