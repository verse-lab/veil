module

public import Veil
public meta import Lean.Util.CollectAxioms

set_option veil.smt.trust false

veil module ReachableExport

type node
param limit : Nat

relation marked (N : node)
function rank : node → Nat

after_init {
  marked N := false
  rank N := 0
}

action mark (n : node) {
  marked n := true
}

invariant [rank_zero] rank N = 0
invariant [marked_zero] marked N → rank N = 0

#gen_spec
#check_invariants
#gen_theorems

-- The ordinary command now exports the induction and both projections.
#check Invariants.is_inv
#check rank_zero.is_inv
#check marked_zero.is_inv

-- Repeating export is harmless and reuses the checked declarations.
#gen_theorems

run_cmd do
  for name in [`ReachableExport.Invariants.is_inv, `ReachableExport.rank_zero.is_inv,
      `ReachableExport.marked_zero.is_inv] do
    if (← Lean.collectAxioms name).contains ``sorryAx then
      throwError "reachable invariant theorem contains an admitted proof: {name}"

end ReachableExport

veil module ReachableConcreteSort

type node
relation marked (N : node)

after_init { marked N := false }
action mark (n : node) { marked n := true }
invariant [self] marked N → marked N

#gen_spec
#check_invariants
#gen_theorems with node := Nat

#check Invariants.is_inv
#check self.is_inv

/--
error: cannot generate reachable-invariant theorem `ReachableConcreteSort.Invariants.is_inv` because a declaration with that name already exists with a different type or sort substitution
-/
#guard_msgs in
#gen_theorems with node := Bool

end ReachableConcreteSort

-- Exporting is independent of selecting work for the solver. In particular,
-- a partial action check must not certify initialization or global safety.
veil module ReachablePartial

individual ready : Bool
after_init { ready := true }
action keep { ready := true }
invariant [ready_inv] ready

#gen_spec

/--
warning: #gen_theorems exported available local lemmas, but omitted reachable-invariant theorems: missing proof obligations [initializer_ready_inv_tr,
 keep_ready_inv_tr]
-/
#guard_msgs in
#gen_theorems

run_cmd do
  let env ← Lean.getEnv
  for name in [`ReachablePartial.Invariants.is_inv, `ReachablePartial.keep_ready_inv,
      `ReachablePartial.initializer_ready_inv] do
    if env.contains name then throwError "export started an unchecked VC: {name}"

#check_action keep

/--
warning: #gen_theorems exported available local lemmas, but omitted reachable-invariant theorems: missing proof obligations [initializer_ready_inv_tr]
-/
#guard_msgs in
#gen_theorems

run_cmd do
  let env ← Lean.getEnv
  unless env.contains `ReachablePartial.keep_ready_inv do
    throwError "partial export omitted its checked action lemma"
  if env.contains `ReachablePartial.Invariants.is_inv then
    throwError "partial export claimed unconditional reachability"

#check_invariants
#gen_theorems
#check ready_inv.is_inv

end ReachablePartial

veil module ReachableDeferredExport

set_option veil.deferVCGeneration true
individual flag : Bool
after_init { flag := false }
action keep { pure () }
invariant [clear] flag = false

#gen_spec

/--
warning: #gen_theorems has no checked verification conditions to export; verification generation is deferred. Run #check_invariants or #check_action first.
-/
#guard_msgs in
#gen_theorems

run_cmd do
  let env ← Lean.getEnv
  for name in [`ReachableDeferredExport.keep.wp,
      `ReachableDeferredExport.relationalTransitionSystem,
      `ReachableDeferredExport.Invariants.is_inv] do
    if env.contains name then
      throwError "export prepared or checked a deferred specification: {name}"

#check_invariants
#gen_theorems
#check clear.is_inv

end ReachableDeferredExport

-- Native transitions already provide their TR certificate; no generated
-- imperative-action derived_eq theorem is required for this induction arm.
veil module ReachableNativeTransition

individual flag : Bool
after_init { flag := false }
transition keep { flag' = flag }
invariant [clear] flag = false

#gen_spec
#check_invariants
#gen_theorems
#check clear.is_inv

end ReachableNativeTransition
