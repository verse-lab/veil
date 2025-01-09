import Veil.DSL

/-
`solve_clause` should not fail (with a "no goals to be solved" error)
when the goal is trivially solvable. This error arises because we call
`withMainContext` when evaluating tactics, but `withMainContext` calls
`throwNoGoalsToBeSolved` if there are no goals.
In particular, `solve_clause` performs some simplifications, which may
solve the goal before `sauto` is called.
-/

#guard_msgs in
example : True := by solve_clause
