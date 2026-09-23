module

public import Veil

public section

set_option veil.smt.trust false
set_option veil.printCounterexamples false
set_option linter.unusedVariables false

open Lean in
meta def checkReachableTheorems (ns : Name) (names : Array Name) (present := true) :
    Elab.Command.CommandElabM Unit := do
  for name in names do
    let fullName := ns ++ name
    if present then
      let env ← getEnv
      let some info := env.find? fullName
        | throwError "expected reachable-invariant theorem {fullName}"
      let axioms ← collectAxioms fullName
      -- Imported public theorems have opaque signatures and recorded provenance.
      unless (info matches .thmInfo _) ||
          ((info matches .axiomInfo _) && (env.getModuleIdxFor? fullName).isSome &&
            !axioms.contains fullName) do
        throwError "expected a proved reachable-invariant theorem {fullName}"
      if axioms.contains ``sorryAx then
        throwError "unexpected sorry in {fullName}"
    else if (← getEnv).contains fullName then
      throwError "unexpected reachable-invariant theorem {fullName}"

veil module ReachableConjunction

type node
relation marked : node → Bool
relation ready : Bool
immutable relation enabled : Bool
#gen_state
assumption enabled
after_init {
  marked N := true
  ready := true
}
action mark (n : node) { marked n := enabled }
transition keep (n : node) { ∀ N, marked' N ↔ marked N }
invariant [all_marked] marked N = true
invariant [is_ready] ready
safety [safe] ready ∧ marked N
safety [safe_again] marked N ∨ ¬ready
#gen_spec
#gen_theorems
#gen_theorems

run_cmd checkReachableTheorems `ReachableConjunction #[`Invariants.is_inv, `all_marked.is_inv, `is_ready.is_inv,
    `safe.is_inv, `safe_again.is_inv, `Safeties.is_inv]

-- The generated statements apply to concrete reachable states.
example {node : Type} [Inhabited node] [DecidableEq node]
    (th : Theory node) (st : State (FieldAbstractType node))
    (hr : (relationalTransitionSystem node).reachable th st) :
    Safeties (ρ := Theory node) (σ := State (FieldAbstractType node)) (node := node) (χ := FieldAbstractType node) th st := Safeties.is_inv th st hr

end ReachableConjunction

veil module ReachableMissingDependency

relation good : Bool
relation support : Bool
#gen_state
after_init { good := true; support := true }
action break_support { support := false }
action follow_support { good := support }
invariant [good_clause] good
invariant [support_clause] support
#gen_spec
#gen_theorems

-- All VCs for good_clause succeed assuming support_clause. Nevertheless good
-- becomes false after break_support; follow_support, so it is not invariant.
run_cmd checkReachableTheorems `ReachableMissingDependency #[`initializer_good_clause, `break_support_good_clause, `follow_support_good_clause]
run_cmd checkReachableTheorems `ReachableMissingDependency #[`break_support_support_clause, `Invariants.is_inv, `good_clause.is_inv,
    `support_clause.is_inv, `Safeties.is_inv] false

end ReachableMissingDependency

veil module ReachableTrustedDependency

relation marked : Bool
#gen_state
after_init { marked := true }
action keep { pure () }
invariant [all_marked] marked
trusted invariant [trusted_clause] True
#gen_spec
#gen_theorems

run_cmd checkReachableTheorems `ReachableTrustedDependency #[`Invariants.is_inv, `all_marked.is_inv, `trusted_clause.is_inv, `Safeties.is_inv] false

-- A trusted clause needs an actual proof before it can support reachability.
theorem trusted_clause.is_inv : relationalTransitionSystem.isInvariant
    (fun th st => trusted_clause th st) := by
  intro th st hr
  trivial

#gen_theorems
run_cmd checkReachableTheorems `ReachableTrustedDependency #[`Invariants.is_inv, `all_marked.is_inv, `trusted_clause.is_inv, `Safeties.is_inv]

end ReachableTrustedDependency

veil module ReachableNoActions

relation marked : Bool
#gen_state
after_init { marked := true }
invariant [all_marked] marked
#gen_spec
#gen_theorems
run_cmd checkReachableTheorems `ReachableNoActions #[`Invariants.is_inv, `all_marked.is_inv, `Safeties.is_inv]

end ReachableNoActions

veil module ReachableNoClauses

relation marked : Bool
#gen_state
after_init { marked := true }
action keep { pure () }
#gen_spec
#gen_theorems
run_cmd checkReachableTheorems `ReachableNoClauses #[`Invariants.is_inv, `Safeties.is_inv]

end ReachableNoClauses

veil module ReachableNameConflict

relation marked : Bool
#gen_state
after_init { marked := true }
action keep { pure () }
invariant [all_marked] marked
#gen_spec

theorem all_marked.is_inv : True := True.intro

/--
error: cannot generate reachable-invariant theorem `ReachableNameConflict.all_marked.is_inv` because a declaration with that name already exists with a different type
-/
#guard_msgs in
#gen_theorems

-- A failed generator must not install partial declarations or sorry proofs.
run_cmd checkReachableTheorems `ReachableNameConflict #[`Invariants.is_inv, `Safeties.is_inv] false

end ReachableNameConflict
