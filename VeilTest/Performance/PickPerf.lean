import Veil

set_option linter.unusedVariables false

/-! # Performance test for partial non-deterministic assignments

This tests that `f ... N ... := *` (where only capitalized args are
universally quantified) picks from a narrowed type, rather than the full
domain type. With 5-domain relations and `node := Fin 2`:
- Full type: `(Fin 2)^5 → Bool`, `2^32` possible functions — intractable.
- Optimized (1 capital): `Fin 2 → Bool`, `4` possible functions — instant.

-/

-- Case 1: Relation
-- Picks from (node → Bool), 2^|node| = 4 options for Fin 2.
-- Without optimization: 2^(|node|^5) = 2^32 options.
veil module PickPerf_Rel

type node
immutable individual na : node
immutable individual nb : node
immutable individual nc : node
immutable individual nd : node
relation rel (a : node) (b : node) (c : node) (d : node) (e : node)
#gen_state
after_init { rel A B C D E := false }
action act { rel na nb N nc nd := * }
invariant true
#gen_spec
#model_check interpreted { node := Fin 2 } { na := 0, nb := 0, nc := 0, nd := 0 }

end PickPerf_Rel

-- Case 2: Function
-- Picks from (node → node), |node|^|node| = 3 options for Fin 3.
-- Without optimization: |node|^(|node|^5)
veil module PickPerf_Fun

type node
immutable individual na : node
immutable individual nb : node
immutable individual nc : node
immutable individual nd : node
function f (a : node) (b : node) (c : node) (d : node) (e : node) : node
#gen_state
after_init { f A B C D E := A }
action act { f na nb N nc nd := * }
invariant true
#gen_spec
#model_check interpreted { node := Fin 3 } { na := 0, nb := 0, nc := 0, nd := 0 }

end PickPerf_Fun

-- Case 3: Relation, partial pick
-- Picks from (node → node → Bool), 2^|node*node| = 16 options for Fin 2.
-- Without optimization: 2^(|node|^5) = 2^32 options.
veil module PickPerf_Rel_Partial

type node
immutable individual na : node
immutable individual nb : node
immutable individual nc : node
relation rel (a : node) (b : node) (c : node) (d : node) (e : node)
#gen_state
after_init { rel A B C D E := false }
action act { rel na nb N nc := * }
invariant true
#gen_spec
#model_check interpreted { node := Fin 2 } { na := 0, nb := 0, nc := 0 }

end PickPerf_Rel_Partial

-- Case 4: No capitals — all arguments are specific values.
-- Picks from Bool (just the codomain), 2 options.
-- Without optimization: 2^32 options.
veil module PickPerf_NoCap

type node
immutable individual na : node
immutable individual nb : node
immutable individual nc : node
immutable individual nd : node
immutable individual ne : node
relation rel (a : node) (b : node) (c : node) (d : node) (e : node)
#gen_state
after_init { rel A B C D E := false }
action act { rel na nb nc nd ne := * }
invariant true
#gen_spec
#model_check interpreted { node := Fin 2 } { na := 0, nb := 0, nc := 0, nd := 0, ne := 0 }

end PickPerf_NoCap
