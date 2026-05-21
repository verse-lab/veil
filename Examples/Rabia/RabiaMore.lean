-- skip eval
import Veil
import Examples.Rabia.Rabia

-- adapted from [weak_mvc.v](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/coq/weak_mvc.v)

inductive state_value where
  | v0 | v1 | vquestion
deriving DecidableEq, Nonempty

instance : ThreeValuedType state_value where
  v0 := state_value.v0
  v1 := state_value.v1
  vquestion := state_value.vquestion
  ax1 := by simp
  ax2 := by simp
  ax3 := by simp
  ax4 := by
    intro x
    cases x <;> simp

instance : TotalOrderWithMinimum Nat where
  le := Nat.le
  le_refl := by simp
  le_trans := by
    simp
    omega
  le_antisymm := by
    simp
    omega
  le_total := by
    simp
    omega

  lt := Nat.lt
  le_lt := by
    simp
    omega

  next x y := y = x + 1
  next_def := by
    simp
    intro x y
    apply Iff.intro
    · intro
      subst_vars
      apply And.intro <;> omega
    · intro ⟨h1, h2⟩
      specialize h2 (x + 1) (by omega)
      omega

  zero := 0
  zero_lt := by simp

veil module Rabia

set_option veil.smt.timeout 120

#time #check_invariants Wrapper1
#time #check_invariants Wrapper2
#time #check_invariants Wrapper3
#time #check_invariants Wrapper4
#time #check_invariants Wrapper5

end Rabia

/-!
The remaining proof script from `main` is intentionally commented out for this
preview port. The isolate checks translate to the active invset checks above,
but the later proof export still depends on `#recover_invariants_in_tr`,
`#split_invariants`, and theorem names generated from those proof steps.

```lean
veil module Rabia

set_option veil.smt.timeout 120

-- Lift to `tr` style those theorems that were originally proven in `wp` style.
#time #recover_invariants_in_tr

prove_inv_inductive by {
  constructor
  . intro st has hinit
    sdestruct_goal <;> already_proven_init
  · intro st st' has hinv hnext
    sts_induction <;> sdestruct_goal <;> already_proven_next_tr
}

#time #split_invariants

end Rabia

namespace Rabia
-- The later `*.is_inv` proofs also depend on generated theorem names.
end Rabia
```
-/
