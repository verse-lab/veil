
import Veil.DSL

variable {node : Type}

example : ∀ x : node, x = x → ¬¬ (x = x) := by solve_clause
