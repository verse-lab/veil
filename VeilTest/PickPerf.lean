import Veil

set_option linter.unusedVariables false

/-! # Performance test for partial non-deterministic assignments

This tests that `f a b c d N := *` (where only `N` is capitalized) picks
from a type that only includes the capitalized dimension, rather than the
full domain type. Without this optimization, the model checker would need
to enumerate all `2^(|node|^5)` possible functions for a 5-ary relation,
which is `2^32` for `Fin 2` — completely intractable. With the
optimization, it only enumerates `2^|node|` = `4` possibilities.
-/

veil module PickPerfTest

type node

-- A relation with 5 domain components.
-- Full type: node → node → node → node → node → Bool
relation bigrel (a : node) (b : node) (c : node) (d : node) (e : node)

-- A function with 5 domain components.
-- Full type: node → node → node → node → node → node
function bigfun (a : node) (b : node) (c : node) (d : node) (e : node) : node

#gen_state

after_init {
  bigrel A B C D E := false
  bigfun A B C D E := A
}

-- Only N is capitalized (universally quantified over the last dimension).
-- With optimization: picks from (node → Bool), 2^|node| options.
-- Without optimization: picks from (node → node → node → node → node → Bool),
--   2^(|node|^5) options.
action modifyRel (a b c d : node) {
  bigrel a b c d N := *
}

-- Only N is capitalized.
-- With optimization: picks from (node → node), |node|^|node| options.
-- Without optimization: picks from (node → node → node → node → node → node),
--   |node|^(|node|^5) options.
action modifyFun (a b c d : node) {
  bigfun a b c d N := *
}

invariant true

#gen_spec

-- With maxDepth := 1, the model checker explores init + one level of successors.
-- With node := Fin 2 and the optimization:
--   Each action has 2^4 = 16 param combos × 4 pick options = 64 candidates.
--   This completes instantly.
-- Without the optimization:
--   Each action would have 16 param combos × 2^32 pick options ≈ 64 billion
--   candidates. This would never complete.
/-- info: ✅ No violation (explored 4651 states) -/
#guard_msgs in
#model_check interpreted { node := Fin 2 } {} (maxDepth := 1)

end PickPerfTest
