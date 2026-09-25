module

public import VeilTest.GenReachableInvariants

public section

open scoped ReachableConjunction

run_cmd checkReachableTheorems `ReachableConjunction #[`Invariants.is_inv, `all_marked.is_inv, `is_ready.is_inv,
    `safe.is_inv, `safe_again.is_inv, `Safeties.is_inv]

example {node : Type} [Inhabited node] [DecidableEq node]
    (th : ReachableConjunction.Theory node)
    (st : ReachableConjunction.State (ReachableConjunction.FieldAbstractType node))
    (hr : (ReachableConjunction.relationalTransitionSystem node).reachable th st) :
    ReachableConjunction.all_marked (ρ := ReachableConjunction.Theory node)
      (σ := ReachableConjunction.State (ReachableConjunction.FieldAbstractType node))
      (node := node) (χ := ReachableConjunction.FieldAbstractType node) th st :=
  ReachableConjunction.all_marked.is_inv th st hr
