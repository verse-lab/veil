-- skip eval
import Veil
import Veil.Model.TransitionSystem
import Benchmarks.Veil.Rabia

-- adapted from [weak_mvc.v](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/coq/weak_mvc.v)

inductive state_value where
  | v0 | v1 | vquestion
deriving DecidableEq, Nonempty

instance : ThreeValuedType state_value where
  v0 := state_value.v0
  v1 := state_value.v1
  vquestion := state_value.vquestion
  ax1 := by simp
  ax2 := by simp
  ax3 := by simp
  ax4 := by intro x ; cases x <;> simp

instance : TotalOrderWithMinimum Nat where
  le := Nat.le
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega

  lt := Nat.lt
  le_lt := by simp ; omega

  next x y := y = x + 1
  next_def := by
    simp ; intro x y ; apply Iff.intro
    next => intro ; subst_vars ; apply And.intro <;> omega
    next => intro ⟨h1, h2⟩ ; specialize h2 (x + 1) (by omega) ; omega

  zero := 0
  zero_lt := by simp

veil module Rabia

set_option veil.smt.timeout 120

-- Instead of this:
-- #time #check_isolates wrapper1 wrapper2 wrapper3 wrapper4 wrapper5
-- We found that this is faster:
-- #time set_option veil.vc_gen "transition" in #time #check_isolates wrapper1 wrapper2 wrapper3 wrapper4 wrapper5


/- NOTE for Artifact Reviewers:

On our (MacBook Pro, M4 processor, 32GB RAM) machine, we ran one of the two
commented-out commands above (either works) to verify the non-`protocol`
isolates in the Rabia specification. This completed without any errors or
timeouts in ~2.5 minutes.

However, we found that on a different machine (Thinkpad X1 Carbon, 13th Gen
Intel(R) Core(TM) i7-1370P, 64GB RAM), these reliably timed out on some
sub-goals. We suspect this might be the case on other `amd64` machines as well,
so in the interest of increasing reproducibility, we provide instead a different
approach of proving the same final theorem:

- We first prove `phase_rnd2_good_succ_good` with the `BigStep` (in fact,
  `TwoState` – we don't care about `action` return values) semantics.

- We then prove all other invariants in the `wrapperN` isolates in the `WP`
  semantics and use the `#recover_invariants_in_tr` command to soundly (via the
  `TwoState_sound'_ret_unit'` theorem) 'lift' these `WP`-style theorems into
  `tr`-style theorems.

=> The end result is equivalent to running either:

```lean
#check_isolates wrapper1 wrapper2 wrapper3 wrapper4 wrapper5
#recover_invariants_in_tr
```

OR

```lean
set_option veil.vc_gen "transition" in #time #check_isolates wrapper1 wrapper2 wrapper3 wrapper4 wrapper5
```

(these have the same behavior)

However, that the approach below, will produce an `unknown` (❓) result for
`phase_rnd2_good_succ_good` in the `WP` semantics. This is OK, as that theorem
is not generated and not used in any way. We run this check with
`set_option veil.failedCheckThrowsError false` to proceed despite the `unknown`
result. The rest of the file compiles without any errors.

-/

#time
@[invProof]
theorem phase_rnd2_tr_good_succ_good :
    ∀ (st st' : @State node set_majority set_f_plus_1 phase proposal_value state_value),
      (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
              set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
              proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
              tv).assumptions
          st →
        (@System node node_dec node_ne set_majority set_majority_dec set_majority_ne set_f_plus_1
                set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec phase_ne tot proposal_value
                proposal_value_dec proposal_value_ne state_value state_value_dec state_value_ne
                tv).inv
            st →
          (@Rabia.phase_rnd2.tr node node_dec node_ne set_majority set_majority_dec
                set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                state_value_dec state_value_ne tv)
              st st' →
            (@Rabia.good_succ_good node node_dec node_ne set_majority set_majority_dec
                set_majority_ne set_f_plus_1 set_f_plus_1_dec set_f_plus_1_ne bg phase phase_dec
                phase_ne tot proposal_value proposal_value_dec proposal_value_ne state_value
                state_value_dec state_value_ne tv)
              st' :=
  by ((unhygienic intros); solve_clause[Rabia.phase_rnd2.tr]Rabia.good_succ_good)

set_option veil.smt.retryOnUnknown false
set_option veil.failedCheckThrowsError false in
#time #check_isolates wrapper1 wrapper2 wrapper3 wrapper4 wrapper5

-- Lift to `tr` style those theorems that were originally proven in `wp` style
#time #recover_invariants_in_tr

prove_inv_inductive by {
  constructor
  . intro st has hinit
    sdestruct_goal <;> already_proven_init
  · intro st st' has hinv hnext
    sts_induction <;> sdestruct_goal <;> already_proven_next_tr
}

#time #split_invariants

end Rabia

namespace Rabia
-- NOTE: here we're doing a bit of a hack to open `veil module Rabia`
-- with `phase` instantiated to `Nat` and `state_value` to the enum type
-- defined above we will eventually support this properly

-- all implicit, required by the invariant definition
--  make more precise? maybe `type [implicit] node`?
variable {node : Type} [node_dec : DecidableEq node] [node_ne : Nonempty node]
  {set_majority : Type} [set_majority_dec : DecidableEq set_majority] [set_majority_ne : Nonempty set_majority]
  {set_f_plus_1 : Type} [set_f_plus_1_dec : DecidableEq set_f_plus_1] [set_f_plus_1_ne : Nonempty set_f_plus_1]
  [bg : Background node set_majority set_f_plus_1]
  {proposal_value : Type} [proposal_value_dec : DecidableEq proposal_value] [proposal_value_ne : Nonempty proposal_value]

abbrev phase := Nat

-- we cannot make everything implicit ... at least they need to be explicit somewhere
abbrev State' node set_majority set_f_plus_1 proposal_value := State node set_majority set_f_plus_1 phase proposal_value state_value

--  the weird namespace issue
--  why ghost relation places the state argument at the end?
def started_good (s : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  ∀ (p : phase), started p s → good p s

--  automatically change the implicit level of the previous `.is_inv`
theorem started_good.is_inv : RelationalTransitionSystem.isInvariant
  (σ := State' node set_majority set_f_plus_1 proposal_value) started_good := by
  intro s hr
  have hgsg := Rabia.good_succ_good.is_inv _ _ _ _ _ _ _ hr
  have hgz0 := Rabia.good_zero.is_inv _ _ _ _ _ _ _ hr
  have hhp := Rabia.started_pred.is_inv _ _ _ _ _ _ _ hr

  intro p hstarted
  induction p with
  | zero => apply hgz0 ; exact hstarted
  | succ p ih =>
    apply hgsg p ; apply And.intro
    next => apply ih ; apply hhp ; apply And.intro ; exact hstarted ; rfl
    next => apply And.intro ; rfl ; exact hstarted

def validity_bc (s : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  ∀ N1 P1 V1, s.decision_bc N1 P1 V1 → ∃ N2, s.vote_rnd1 N2 0 V1

theorem validity_bc.is_inv : RelationalTransitionSystem.isInvariant
  (σ := State' node set_majority set_f_plus_1 proposal_value) validity_bc := by
  intro s hr
  have hdr1 := Rabia.decision_bc_vote_rnd1.is_inv _ _ _ _ _ _ _ hr
  have hvr1_pred_r1 := Rabia.vote_rnd1_pred_rnd.is_inv _ _ _ _ _ _ _ hr

  suffices h : (∀ N1 P1 V1, s.vote_rnd1 N1 P1 V1 → ∃ N2, s.vote_rnd1 N2 0 V1) by
    intro n p v hh
    specialize hdr1 _ _ _ hh ; rcases hdr1 with ⟨n', hdr1⟩
    solve_by_elim
  intro n p
  induction p generalizing n with
  | zero => solve_by_elim
  | succ p ih =>
    intro v h
    specialize hvr1_pred_r1 _ _ _ _ ⟨h, rfl⟩ ; rcases hvr1_pred_r1 with ⟨n'', hvr1_pred_r1⟩
    solve_by_elim

def agreement_bc (s : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  ∀ N1 P1 V1 N2 P2 V2,
    s.decision_bc N1 P1 V1 →
    s.decision_bc N2 P2 V2 →
    V1 = V2

theorem agreement_bc.is_inv : RelationalTransitionSystem.isInvariant
  (σ := State' node set_majority set_f_plus_1 proposal_value) agreement_bc := by
  intro s hr
  have hstarted := started_good.is_inv _ hr
  have hvld_agree := Rabia.vl_decision_bc_agree.is_inv _ _ _ _ _ _ _ hr
  have hdsr_agree := Rabia.decision_bc_same_round_agree.is_inv _ _ _ _ _ _ _ hr
  have hdstarted := Rabia.decision_bc_started.is_inv _ _ _ _ _ _ _ hr

  suffices h : (∀ N1 P1 V1 N2 P2 V2,
    P1 ≤ P2 →
    s.decision_bc N1 P1 V1 →
    s.decision_bc N2 P2 V2 →
    V1 = V2) by
    intro n1 p1 vv1 n2 p2 vv2
    by_cases hh : p1 ≤ p2
    next => apply h ; assumption
    next =>
      intro h1 h2 ; symm ; revert h1 ; revert h2 ; apply h
      unfold phase at * ; omega   -- `phase` will puzzle `omega`
  intro n1 p1 vv1 n2 p2 vv2 hle hdec1 hdec2
  by_cases p1 = p2
  next => subst_vars ; apply hdsr_agree ; solve_by_elim
  next hneq =>
    have hlt : p1 < p2 := by unfold phase at * ; omega
    clear hle hneq
    have hh : state_value_locked p2 vv1 s := by
      --  change these into something like `whnf`?
      dsimp [decision_bc_started] at hdstarted
      have hgood P hh := hstarted P hh |>.right |>.right
      dsimp only [started] at hgood ; simp only [and_imp] at hgood
      apply hgood <;> solve_by_elim
    apply hvld_agree <;> solve_by_elim

/- `agreement1` (`decision_full_val_agree`) is already proven -/
#check Rabia.decision_full_val_agree.is_inv

def agreement2 (s : State' node set_majority set_f_plus_1 proposal_value) : Prop :=
  ∀ N1 P1 V1 N2 P2,
    s.decision_full_val N1 P1 V1 →
    s.decision_full_noval N2 P2 → False

theorem agreement2.is_inv : RelationalTransitionSystem.isInvariant
  (σ := State' node set_majority set_f_plus_1 proposal_value) agreement2 := by
  intro s hr
  have ha := Rabia.decision_full_val_inv.is_inv _ _ _ _ _ _ _ hr
  have hb := Rabia.decision_full_noval_inv.is_inv _ _ _ _ _ _ _ hr
  have hc := agreement_bc.is_inv _ hr

  intro n1 p1 vv1 n2 p2 hdec1 hdec2
  suffices state_value.v0 = state_value.v1 by contradiction
  specialize ha _ _ _ hdec1
  specialize hb _ _ hdec2
  solve_by_elim

/- `validity` (`decision_full_val_validity`) is already proven -/
#check Rabia.decision_full_val_validity.is_inv

end Rabia
