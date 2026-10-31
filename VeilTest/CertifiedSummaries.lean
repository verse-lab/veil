module

public import Veil
public import Veil.Frontend.DSL.Action.Semantics.Contracts

set_option veil.smt.trust false
set_option veil.solver "grind+smt"

veil module CertifiedSummarySource

type tx
relation finalized : tx → Bool

after_init { finalized T := false }

action finalize (t : tx) {
  finalized t := true
  ensure ∀ u : tx, old(finalized u) → finalized u
}

#gen_spec
end CertifiedSummarySource

veil module CertifiedSummaryAdapter

type tx
param source : CertifiedSummarySource tx
relation relayed : tx → Bool
after_init { relayed T := false }

action relay (t : tx) {
  require source.finalized t
  relayed t := true
}

invariant [relay_backed] ∀ t : tx, relayed t → source.finalized t

#gen_spec
end CertifiedSummaryAdapter

veil module SummaryComposition

type tx
isolate s : CertifiedSummarySource (tx := tx)
isolate a : CertifiedSummaryAdapter (tx := tx) (source := s) with s

#gen_spec
#guard_msgs(error, drop info, drop warning) in
#check_invariants
#gen_theorems

abbrev AbstractState (tx : Type) := State (FieldAbstractType tx)

def sourceFinalized {tx : Type} (state : AbstractState tx) : tx → Bool :=
  state.inst_1_s__field__finalized

def adapterRelayed {tx : Type} (state : AbstractState tx) : tx → Bool :=
  state.inst_1_a__field__relayed

def sourceGuarantee (tx : Type) : Transition (Theory tx) (AbstractState tx) :=
  fun _ before after =>
    (∀ u, sourceFinalized before u → sourceFinalized after u) ∧
      adapterRelayed after = adapterRelayed before

open Classical in
theorem finalize_summary {tx : Type} [DecidableEq tx] [Inhabited tx] (t : tx) :
    TransitionSummary
      (inst_1_s__procedure__finalize.ext.tr (ρ := Theory tx) (σ := AbstractState tx) (tx := tx)
        (χ := FieldAbstractType tx) t)
      (fun _ _ => True) (sourceGuarantee tx) := by
  constructor
  intro th before after _ hstep
  simp only [nextSimp, substateSimp] at hstep
  dsimp [IsSubStateOf.getFrom, IsSubStateOf.setIn, instIsSubStateOfRefl] at hstep
  simp only [sourceGuarantee, sourceFinalized, adapterRelayed]
  split at hstep
  · subst after
    constructor
    · intro u hu
      dsimp
      split <;> simp_all
    · rfl
  · exact False.elim (hstep trivial)

-- This is the concrete foreign-step preservation VC. Its proof applies the
-- closed provider certificate and uses only growth + frame; it never unfolds
-- `finalize`, its WP, or its transition relation.
open Classical in
theorem relay_backed_under_finalize
    {tx : Type} [DecidableEq tx] [Inhabited tx] (t : tx) :
    Transition.meetsSpecificationIfSuccessfulAssuming
      (inst_1_s__procedure__finalize.ext.tr (ρ := Theory tx) (σ := AbstractState tx) (tx := tx)
        (χ := FieldAbstractType tx) t)
      (fun _ => True)
      (fun _ state => ∀ u, adapterRelayed state u → sourceFinalized state u)
      (fun _ state => ∀ u, adapterRelayed state u → sourceFinalized state u) := by
  apply (finalize_summary t).preserves
  · intros; trivial
  · intro th before after _ hbacked hsummary u hrelayed
    exact hsummary.1 u (hbacked u (by simpa only [hsummary.2] using hrelayed))

run_cmd do
  for name in [`SummaryComposition.finalize_summary,
      `SummaryComposition.relay_backed_under_finalize] do
    if (← Lean.collectAxioms name).contains ``sorryAx then
      throwError "summary proof contains an admitted proof: {name}"
  let info ← Lean.getConstInfo `SummaryComposition.relay_backed_under_finalize
  let some proof := info.value? (allowOpaque := true) | throwError "expected a proved summary client theorem"
  unless proof.getUsedConstants.contains `SummaryComposition.finalize_summary do
    throwError "client proof did not apply the provider certificate"

end SummaryComposition
