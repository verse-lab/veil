module

public import Veil

set_option veil.smt.trust false
set_option veil.printCounterexamples false

veil module InvSetSupport

individual source_bit : Bool
individual sink_bit : Bool

after_init {
  source_bit := false
  sink_bit := false
}

action copy { sink_bit := source_bit }

invset Source {
  invariant [source_clear] source_bit = false
}

invset Sink extends Source {
  invariant [sink_clear] sink_bit = false
}

#gen_spec
#check_invariants Sink
#check_invariants
#gen_theorems
#check sink_clear.is_inv

run_cmd do
  let mod ← Veil.getCurrentModule
  let support ← mod.resolveInvSetSupport `Sink
  unless support.contains `source_clear && support.contains `sink_clear do
    throwError "extends failed to retain the target and source invariants"

/--
error: `using` overrides require separate proof provenance and are not supported yet; declare the desired support with `invset ... extends ...`
-/
#guard_msgs in
#check_invariants Sink using Source

end InvSetSupport

-- The full pre-state invariant is inconsistent. An unrestricted discharger
-- could prove any preservation VC from it. The selected sink proof must
-- discard that unrelated false hypothesis and expose its missing source fact.
veil module InvSetExcludesContradiction

individual source_bit : Bool
individual sink_bit : Bool

after_init {
  source_bit := false
  sink_bit := false
}

action copy { sink_bit := source_bit }

invset Noise {
  invariant [unrelated_false] False
}

invset Sink {
  invariant [sink_clear] sink_bit = false
}

#gen_spec

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  sink_clear ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  copy
    doesNotThrow ... ✅
    sink_clear ... ❌
-/
#guard_msgs(error, drop info, drop warning) in
#check_invariants Sink

end InvSetExcludesContradiction

-- Numeric state and an old-state postcondition must retain the ordinary
-- field abstraction after support restriction, including assertion freedom.
veil module NumericInvSetSupport

param limit : Nat
individual value : Nat
after_init { value := 0 }

action increment {
  require value < limit
  value := value + 1
  ensure old(value) ≤ value
}

invset Counter {
  invariant [bounded] value ≤ limit
}
invariant [irrelevant] True

#gen_spec

open Lean Elab Command in
run_cmd do
  let mgr ← Veil.Verifier.vcManager.atomically fun ref => ref.get
  let some (_, vc) := mgr.nodes.toArray.find? (fun (_, vc) =>
      vc.name == `increment_doesNotThrow)
    | throwError "missing concrete numeric assertion-freedom VC"
  liftTermElabM do
    let statementType ← vc.toVCStatement.type
    let boundedId := Lean.mkIdent `bounded
    let script ← `(term| by
      veil_restrict_invset_pre [$boundedId:ident]
      veil_apply_local_wp
      __veil_solve_wplo)
    let proof ← Term.withoutErrToSorry <| Term.elabTermEnsuringType script statementType
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasFVar || proof.hasSorry then
      throwError "restricted numeric assertion-freedom proof is incomplete"
    discard <| Veil.addVeilTheorem `restricted_increment_doesNotThrow statementType proof

#check_invariants Counter
#check_invariants
#gen_theorems
#check bounded.is_inv

end NumericInvSetSupport

veil module InvSetBadReferences

individual flag : Bool
after_init { flag := false }
action keep { pure () }
invariant [flag_clear] flag = false

invset CycleA extends CycleB := { flag_clear }
invset CycleB extends CycleA := { flag_clear }

/-- error: cyclic invset extends chain involving CycleA -/
#guard_msgs in
#gen_spec

end InvSetBadReferences
