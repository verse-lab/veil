import Veil
import Veil.Liveness

/-! # Tiny Consensus Specification

Encoding of the PlusCal/TLA+ `Consensus` example from https://github.com/tlaplus/Examples/blob/master/specifications/byzpaxos/Consensus.tla
-/

veil module Consensus

open TLA

type value

relation chosen : value → Bool

#gen_state

after_init {
  chosen V := false
}

ghost relation noneChosen := ∀ v, ¬ chosen v
ghost relation someChosen := ∃ v, chosen v

action choose {
  require noneChosen
  let v ← pick value
  chosen v := true
}

action stutter {
  pure ()
}

safety [agreement] chosen V1 ∧ chosen V2 → V1 = V2

set_option veil.smt.trust false

#gen_spec

#check_invariants

temporal [success] 𝒲ℱ choose → ◇ ⌜ someChosen ⌝

prove_temporal_by [success]
  -- Name each of the three conjuncts: ⌜ Init ⌝, □⟨ NextStep ⟩ and □⌜ Invariants ⌝
  tstart hInit hNext hInv
  tclear hInv             -- the agreement invariant is not needed for this proof
  tdsimp only [success]   -- unfold `success`
  tintro hwf              -- introduce hwf : weak fairness of `choose` to the
                          -- temporal proof context

  -- Part 1: reduce the goal to `noneChosen ↝ someChosen`
  tsuffices hleadsto :
   ⌜fun st => (veil_term% noneChosen) st⌝ ↝ ⌜fun st => (veil_term% someChosen) st⌝ by
    tunfold leads_to at hleadsto           -- unfold leads-to to expose the outer □
    thave himp := always_weaken _ hleadsto -- fix it at the initial position
    tapply himp                            -- prove with `noneChosen` as the state
    tclear *- hInit                        -- clear unrelated temporal hypotheses
    veil_solve_temporal                    -- reduce the goal to FO VC and prove it

  -- Part 2: prove the leads-to via WF1:
  -- `p = noneChosen`, `q = someChosen`, `next = NextStep`, and `a = choose`
  tclear hInit                             -- ⌜ Init ⌝ is not used here
  trevert hNext hwf ; trewrite [← TLA.and_imp]
                                           -- massage the goal to match it with
                                           --   the conclusion of `wf1_original`
  tapply wf1_original                      -- leaves the three obligations
  tsplit_ands
  --  (1) noneChosen is stable until someChosen
  --  (2) a `choose` step achieves someChosen
  --  (3) `choose` is enabled while noneChosen holds
  --  Each is about one transition: strip the outer □,
  --                                reduce to first-order VC and discharge it
  all_goals tmonotone ; veil_solve_temporal

end Consensus
