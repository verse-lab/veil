
import Veil.DSL

variable {node : Type}

#guard_msgs(drop warning) in
example : ∀ x : node, x = x → ¬¬ (x = x) := by solve_clause
