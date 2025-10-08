import Veil.Frontend.DSL.Action.Extraction.Basic
import Veil.Frontend.DSL.Action.Semantics.Theorems

namespace Veil

open MultiExtractor

open AngelicChoice in
open TotalCorrectness in
noncomputable
instance
  {hd : ε → Prop}
  [IsHandler hd]
  : LawfulMonadPersistentLog κ (VeilMultiExecM κ ε ρ σ) (ρ → σ → Prop) where
  log_sound := by
    introv
    simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ,
      StateT.map, ExceptT.mk, TsilTCore.op,
      MonadPersistentLog.log, MonadLift.monadLift, StateT.lift, ExceptT.lift, PeDivM.log,
      PeDivM.prepend, ExceptT.TsilTCore.go, pure, bind, ExceptT.pure]
    ext a b
    simp [pointwiseSup, OfHd, MAlgExcept, MAlgOrdered.μ, Functor.map, PeDivM.prepend, Except.getD]
    simp [LE.pure]

open AngelicChoice TotalCorrectness in
theorem VeilM.extract_list_eq_wp (s : VeilM m ρ σ α)
  (ex : MultiExtractor.ExtractNonDet (ExtCandidates Candidates κ) s)
  (hd : ℤ → Prop) [IsHandler hd] :
  wp s post = wp (s.extractList κ (VeilMultiExecM κ ExId ρ σ) ex) post := by
  apply ExtractNonDet.extract_list_eq_wp

-- a state is in the extraction result iff it is a possible next state
lemma important1
  (act : VeilM m ρ σ α)
  (ex : MultiExtractor.ExtractNonDet (ExtCandidates Candidates κ) act) :
  letI res := NonDetT.extractList κ (VeilMultiExecM κ ExId ρ σ) act ex r₀ s₀
  (∃ a log, (log, DivM.res <| Except.ok (a, s₁)) ∈ res) ↔
  act.toTransition r₀ s₀ s₁ := by
  unfold VeilM.toTransition triple
  -- TODO this is a mess. needs to be cleaned up
  rw [VeilM.extract_list_eq_wp act ex]
  simp [LE.le]
  simp [ReaderT.wp_eq, StateT.wp_eq, AngelicChoice.TsilT.wp_eq, wp_except_handler_eq, PeDivM.wp_eq_DivM, TotalCorrectness.DivM.wp_eq]
  simp [pointwiseSup]
  constructor
  · rintro ⟨a, log, h⟩ --r s hrs
    exists _ , h
  · rintro ⟨a, hin, h⟩
    rcases a with ⟨k, ⟨e | ⟨a, s⟩⟩ | a⟩ <;> simp at h
    subst_eqs ; exists a , k

-- an exception is in the extraction result iff it can be raised
lemma important2
  (e : ExId)
  (act : VeilM m ρ σ α)
  (ex : MultiExtractor.ExtractNonDet (ExtCandidates Candidates κ) act) :
  let _ : IsHandler (· = e) := ⟨⟩
  letI res := NonDetT.extractList κ (VeilMultiExecM κ ExId ρ σ) act ex r₀ s₀
  letI tmp := (open AngelicChoice TotalCorrectness in
    wp act ⊥ r₀ s₀)
  (∃ log, (log, DivM.res <| Except.error e) ∈ res) ↔ tmp := by
  intro hd
  rw [VeilM.extract_list_eq_wp act ex]
  simp [ReaderT.wp_eq, StateT.wp_eq, AngelicChoice.TsilT.wp_eq, wp_except_handler_eq, PeDivM.wp_eq_DivM, TotalCorrectness.DivM.wp_eq]
  simp [pointwiseSup]
  constructor
  · rintro ⟨log, h⟩ --r s hrs
    exists _ , h ; simp
  · rintro ⟨a, hin, h⟩
    rcases a with ⟨k, ⟨e' | ⟨a, s⟩⟩ | a⟩ <;> simp [LE.pure] at h
    subst_eqs ; exists k

end Veil
