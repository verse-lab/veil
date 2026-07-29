import Veil

veil module OptiRBC

type party      -- protocol participants
type val        -- values that can be proposed

-- Quorum types (abstract witnesses for threshold sets of parties)
type opt_quorum
type maj_quorum
type classic_quorum
type amplification_quorum
type commit_quorum

--------------------------------------------------------------------------------
-- Immutable state (theory parameters)
--------------------------------------------------------------------------------

immutable individual broadcaster : party
immutable relation faulty : party → Bool

immutable relation opt_quorum_member : opt_quorum → party → Bool
immutable relation maj_quorum_member : maj_quorum → party → Bool
immutable relation classic_quorum_member : classic_quorum → party → Bool
immutable relation amplification_quorum_member : amplification_quorum → party → Bool
immutable relation commit_quorum_member : commit_quorum → party → Bool

--------------------------------------------------------------------------------
-- Mutable state
--------------------------------------------------------------------------------

relation proposal : val → Bool
relation echo : party → val → Bool
relation vote : party → val → Bool
relation ack : party → val → Bool
relation ready : party → val → Bool
relation committed : party → val → Bool

immutable individual pv : val -- proposal of the non-faulty broadcaster (if any)

#gen_state

--------------------------------------------------------------------------------
-- Abstract domain model assumptions (quorum intersection properties)
--------------------------------------------------------------------------------

-- classic, vote, and optimistic quorums do not contain the broadcaster
assumption [broadcaster_not_in_classic_quorum]
  ∀ (q : classic_quorum), ¬ classic_quorum_member q broadcaster

assumption [broadcaster_not_in_maj_quorum]
  ∀ (q : maj_quorum), ¬ maj_quorum_member q broadcaster

assumption [broadcaster_not_in_opt_quorum]
  ∀ (q : opt_quorum), ¬ opt_quorum_member q broadcaster

-- the set of non-faulty parties satisfies all the quorum thresholds except the optimistic quorum threshold

assumption [non_faulty_commit_quorum]
  (∃ (q : commit_quorum), ∀ p, commit_quorum_member q p → ¬ faulty p)

assumption [non_faulty_amplification_quorum]
  (∃ (q : amplification_quorum), ∀ p, amplification_quorum_member q p → ¬ faulty p)

assumption [non_faulty_maj_quorum]
  (∃ (q : maj_quorum), ∀ p, maj_quorum_member q p → ¬ faulty p)

assumption [non_faulty_classic_quorum]
  (∃ (q : classic_quorum), ∀ p, classic_quorum_member q p → ¬ faulty p)

-- An optimistic quorum contains a non-faulty member.
assumption [opt_quorum_has_nonfaulty_member]
  ∀ (q : opt_quorum), ∃ p, ¬ faulty p ∧ opt_quorum_member q p

-- When the broadcaster is faulty, any two optimistic quorums share a
-- non-faulty member.
assumption [opt_quorum_intersection]
  ∀ (q₁ q₂ : opt_quorum),
    faulty broadcaster →
      (∃ p, ¬ faulty p ∧ opt_quorum_member q₁ p ∧ opt_quorum_member q₂ p)

-- When the broadcaster is faulty, an optimistic quorum and a majority
-- quorum share a non-faulty member.
assumption [opt_maj_quorum_intersection]
  ∀ (q₁ : opt_quorum) (q₂ : maj_quorum),
    faulty broadcaster →
      (∃ p, ¬ faulty p ∧ opt_quorum_member q₁ p ∧ maj_quorum_member q₂ p)

-- When the broadcaster is faulty, an optimistic quorum and a classic quorum
-- share a non-faulty member.
assumption [opt_quorum_intersects_classic_quorum]
  ∀ (q₁ : opt_quorum) (q₂ : classic_quorum),
    faulty broadcaster →
      (∃ p, ¬ faulty p ∧ opt_quorum_member q₁ p ∧ classic_quorum_member q₂ p)

-- When the broadcaster is faulty, any two classic quorums share a non-faulty member.
assumption [classic_quorum_intersection]
  ∀ (q₁ q₂ : classic_quorum),
    faulty broadcaster →
      (∃ p, ¬ faulty p ∧ classic_quorum_member q₁ p ∧ classic_quorum_member q₂ p)

-- Every classic quorum contains a non-faulty member.
assumption [quorum_not_faulty]
  ∀ (q : classic_quorum), ∃ p, ¬ faulty p ∧ classic_quorum_member q p

-- Every majority quorum contains a non-faulty member.
assumption [maj_quorum_has_nonfaulty_member]
  ∀ (q : maj_quorum), ∃ p, ¬ faulty p ∧ maj_quorum_member q p

-- Every amplification quorum contains a non-faulty member.
assumption [amplification_quorum_has_nonfaulty_member]
  ∀ (q : amplification_quorum), ∃ p, ¬ faulty p ∧ amplification_quorum_member q p

-- When the broadcaster is faulty, for any optimistic quorum there exists a
-- majority quorum whose members are all non-faulty and in the optimistic quorum.
assumption [opt_quorum_contains_maj_quorum]
  ∀ (q : opt_quorum),
    faulty broadcaster →
      (∃ (q' : maj_quorum), ∀ p, maj_quorum_member q' p → ¬ faulty p ∧ opt_quorum_member q p)

-- For any commit quorum there exists an amplification quorum whose members
-- are all non-faulty and in the commit quorum.
assumption [commit_quorum_contains_non_faulty_amplification_quorum]
  ∀ (q : commit_quorum),
    ∃ (q' : amplification_quorum), ∀ p, amplification_quorum_member q' p → ¬ faulty p ∧ commit_quorum_member q p


-- #print Theory

--------------------------------------------------------------------------------
-- Initialization
--------------------------------------------------------------------------------

after_init {
  proposal V := false
  echo P V := false
  vote P V := false
  ack P V := false
  ready P V := false
  committed P V := false
}

--------------------------------------------------------------------------------
-- Protocol actions
--------------------------------------------------------------------------------

-- Enabledness condition:
ghost relation propose_enabled :=
  ¬ faulty broadcaster ∧ ∀  v, ¬ proposal v

-- Enabledness condition:
ghost relation echo_enabled (p : party) (v : val):=
   ¬ faulty p ∧ p ≠ broadcaster ∧ (∀ v', ¬ echo p v') ∧ proposal v

ghost relation vote_enabled (p : party) (v : val) :=
  ¬ faulty p ∧ p ≠ broadcaster ∧ (∀ v', ¬ vote p v') ∧ (∃ (q : maj_quorum), ∀ p', maj_quorum_member q p' → echo p' v)


ghost relation ack_enabled (p : party) (v : val) :=
  ¬ faulty p ∧ p ≠ broadcaster ∧ (∀ v', ¬ ack p v') ∧
    ((∃ (q : classic_quorum), ∀ p', classic_quorum_member q p' → vote p' v)
      ∨ (∃ (q : classic_quorum), ∀ p', classic_quorum_member q p' → echo p' v))

ghost relation ready_enabled (p : party) (v : val) :=
  ¬ faulty p ∧ (∀ v', ¬ ready p v') ∧
    ((∃ (q : classic_quorum), ∀ p', classic_quorum_member q p' → ack p' v)
      ∨ (∃ (q : amplification_quorum), ∀ p', amplification_quorum_member q p' → ready p' v))


ghost relation commit_enabled (p : party) (v : val) :=
  ¬ faulty p ∧ (∀ v', ¬ committed p v')
  ∧ (∃ (q : commit_quorum), ∀ p', commit_quorum_member q p' → ready p' v)



action check_totality (p1 : party) (p2 : party) (v : val) {
  require ¬ faulty p1 ∧ ¬ faulty p2
  require committed p1 v
  require ¬ propose_enabled
  require ∀ p v, ¬ echo_enabled p v
  require ∀ p v, ¬ vote_enabled p v
  require ∀ p v, ¬ ack_enabled p v
  require ∀ p v, ¬ ready_enabled p v
  require ∀ p v, ¬ commit_enabled p v
  assert committed p2 v
}

-- Invariants

-- inv0: non-faulty parties never echo, vote, ack, ready, or commit two different values
invariant [inv0]
  ∀ p v1 v2, ¬ faulty p ∧ v1 ≠ v2 →
    ¬ (echo p v1 ∧ echo p v2)
    ∧ ¬ (vote p v1 ∧ vote p v2)
    ∧ ¬ (ack p v1 ∧ ack p v2)
    ∧ ¬ (ready p v1 ∧ ready p v2)
    ∧ ¬ (committed p v1 ∧ committed p v2)

-- inv1: If a non-faulty party commits value v, then either
--   (a) an amplification quorum of non-faulty parties are ready for v, or
--   (b) the non-faulty members of some optimistic quorum have echoed v.
invariant [inv1]
  ∀ p v, ¬ faulty p ∧ committed p v →
    (∃ (q : amplification_quorum), ∀ p', amplification_quorum_member q p' → ¬ faulty p' ∧ ready p' v)
    ∨ (∃ (q : opt_quorum), ∀ p', opt_quorum_member q p' ∧ ¬ faulty p' → echo p' v)

-- inv2: If a non-faulty party is ready for v, then the non-faulty members of
-- some classic quorum have acked v.
invariant [inv2]
  ∀ p v, ¬ faulty p ∧ ready p v →
    (∃ (q : classic_quorum), ∀ p', classic_quorum_member q p' ∧ ¬ faulty p' → ack p' v)

-- inv3: If a non-faulty party has acked v, then either
--   (a) the non-faulty members of some classic quorum have all voted for v, or
--   (b) the non-faulty members of some classic quorum have all echoed v.
invariant [inv3]
  ∀ p v, ¬ faulty p ∧ ack p v →
    (∃ (q : classic_quorum), ∀ p', classic_quorum_member q p' ∧ ¬ faulty p' → vote p' v)
    ∨ (∃ (q : classic_quorum), ∀ p', classic_quorum_member q p' ∧ ¬ faulty p' → echo p' v)

-- inv5: if a non-faulty party votes for v, then the non-faulty members of some majority quorum have echoed v.
invariant [inv5]
  ∀ p v, ¬ faulty p ∧ vote p v →
    (∃ (q : maj_quorum), ∀ p', maj_quorum_member q p' ∧ ¬ faulty p' → echo p' v)

-- Agreement: no two non-faulty parties commit different values.
safety [agreement]
  ∀ p1 p2 v1 v2, ¬ faulty p1 ∧ ¬ faulty p2 ∧ committed p1 v1 ∧ committed p2 v2 → v1 = v2

-- inv7: if the broadcaster is not faulty, then it makes at most one proposal and non-faulty parties only echo, vote, ack, ready, or commit the value proposed by the broadcaster.
invariant [inv7] ¬ faulty broadcaster →
  (∀ v , proposal v → v = pv)
  ∧ ∀ p v, ¬ faulty p →
    (echo p v → proposal v) ∧
    (vote p v → proposal v) ∧
    (ack p v → proposal v) ∧
    (ready p v → proposal v) ∧
    (committed p v → proposal v)

-- The next two are not strictly necessary but it seems they speed things up.

-- inv4: no two non-faulty parties are ready for different values.
invariant [inv4]
  ∀ p1 p2 v1 v2, ¬ faulty p1 ∧ ¬ faulty p2 ∧ ready p1 v1 ∧ ready p2 v2 → v1 = v2

-- inv6: if an optimistic quorum has echoed v, then no non-faulty party votes for a different value.
invariant [inv6] ∀ v,
  (∃ (q : opt_quorum), ∀ p', opt_quorum_member q p' ∧ ¬ faulty p' → echo p' v) →
    (∀ p v', ¬ faulty p ∧ vote p v' → v' = v)

-- inv8: if an optimistic quorum echoes some value, then no non-faulty party
-- acks a different value.
invariant [inv8] ∀ (q : opt_quorum) (v2 : val),
  (∀ p2, opt_quorum_member q p2 ∧ ¬ faulty p2 → echo p2 v2) →
    (∀ p1 v1, ¬ faulty p1 ∧ v1 ≠ v2 → ¬ ack p1 v1)

-- inv9: if the broadcaster is not faulty and a non-faulty party commits, then
-- the broadcaster has proposed.
invariant [inv9] ∀ p v,
  ¬ faulty broadcaster ∧ ¬ faulty p ∧ committed p v → proposal pv

set_option veil.smt.timeout 10

#gen_spec

@[veil]
theorem check_totality_doesNotThrow (ρ : Type) (σ : Type) (party : Type) [party_dec_eq : DecidableEq.{1} party]
    [party_inhabited : Inhabited.{1} party] (val : Type) [val_dec_eq : DecidableEq.{1} val]
    [val_inhabited : Inhabited.{1} val] (opt_quorum : Type) [opt_quorum_dec_eq : DecidableEq.{1} opt_quorum]
    [opt_quorum_inhabited : Inhabited.{1} opt_quorum] (maj_quorum : Type)
    [maj_quorum_dec_eq : DecidableEq.{1} maj_quorum] [maj_quorum_inhabited : Inhabited.{1} maj_quorum]
    (classic_quorum : Type) [classic_quorum_dec_eq : DecidableEq.{1} classic_quorum]
    [classic_quorum_inhabited : Inhabited.{1} classic_quorum] (amplification_quorum : Type)
    [amplification_quorum_dec_eq : DecidableEq.{1} amplification_quorum]
    [amplification_quorum_inhabited : Inhabited.{1} amplification_quorum] (commit_quorum : Type)
    [commit_quorum_dec_eq : DecidableEq.{1} commit_quorum] [commit_quorum_inhabited : Inhabited.{1} commit_quorum]
    (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation
          (State.Label.toDomain party val opt_quorum maj_quorum classic_quorum amplification_quorum commit_quorum
            __veil_f)
          (State.Label.toCodomain party val opt_quorum maj_quorum classic_quorum amplification_quorum commit_quorum
            __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation
          (State.Label.toDomain party val opt_quorum maj_quorum classic_quorum amplification_quorum commit_quorum
            __veil_f)
          (State.Label.toCodomain party val opt_quorum maj_quorum classic_quorum amplification_quorum commit_quorum
            __veil_f)
          (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ]
    [ρ_sub :
      IsSubReaderOf (@Theory party val opt_quorum maj_quorum classic_quorum amplification_quorum commit_quorum) ρ]
    [check_totality_dec_0 :
      delta%
        @OptiRBC.check_totality._veil_dec_type_0 χ party val opt_quorum maj_quorum classic_quorum amplification_quorum
          commit_quorum χ_rep]
    [check_totality_dec_1 :
      delta%
        @OptiRBC.check_totality._veil_dec_type_1 χ party val opt_quorum maj_quorum classic_quorum amplification_quorum
          commit_quorum χ_rep]
    [check_totality_dec_2 :
      delta%
        @OptiRBC.check_totality._veil_dec_type_2 χ party val opt_quorum maj_quorum classic_quorum amplification_quorum
          commit_quorum χ_rep]
    [check_totality_dec_3 :
      delta%
        @OptiRBC.check_totality._veil_dec_type_3 χ party val opt_quorum maj_quorum classic_quorum amplification_quorum
          commit_quorum χ_rep]
    [check_totality_dec_4 :
      delta%
        @OptiRBC.check_totality._veil_dec_type_4 χ party val opt_quorum maj_quorum classic_quorum amplification_quorum
          commit_quorum χ_rep]
    [check_totality_dec_5 :
      delta%
        @OptiRBC.check_totality._veil_dec_type_5 χ party val opt_quorum maj_quorum classic_quorum amplification_quorum
          commit_quorum χ_rep] :
    ∀ (p1 : party) (p2 : party) (v : val) (__veil_ex : Int),
      Veil.VeilM.doesNotThrowAssuming_ex
        (@check_totality.ext ρ σ party party_dec_eq party_inhabited val val_dec_eq val_inhabited opt_quorum
          opt_quorum_dec_eq opt_quorum_inhabited maj_quorum maj_quorum_dec_eq maj_quorum_inhabited classic_quorum
          classic_quorum_dec_eq classic_quorum_inhabited amplification_quorum amplification_quorum_dec_eq
          amplification_quorum_inhabited commit_quorum commit_quorum_dec_eq commit_quorum_inhabited χ χ_rep χ_rep_lawful
          σ_sub ρ_sub check_totality_dec_0 check_totality_dec_1 check_totality_dec_2 check_totality_dec_3
          check_totality_dec_4 check_totality_dec_5 p1 p2 v)
        (@Assumptions ρ party party_dec_eq party_inhabited val val_dec_eq val_inhabited opt_quorum opt_quorum_dec_eq
          opt_quorum_inhabited maj_quorum maj_quorum_dec_eq maj_quorum_inhabited classic_quorum classic_quorum_dec_eq
          classic_quorum_inhabited amplification_quorum amplification_quorum_dec_eq amplification_quorum_inhabited
          commit_quorum commit_quorum_dec_eq commit_quorum_inhabited ρ_sub)
        (@Invariants ρ σ party party_dec_eq party_inhabited val val_dec_eq val_inhabited opt_quorum opt_quorum_dec_eq
          opt_quorum_inhabited maj_quorum maj_quorum_dec_eq maj_quorum_inhabited classic_quorum classic_quorum_dec_eq
          classic_quorum_inhabited amplification_quorum amplification_quorum_dec_eq amplification_quorum_inhabited
          commit_quorum commit_quorum_dec_eq commit_quorum_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub)
    __veil_ex := by
  unveil
  intro hfp1 hfp2 hcp1 h_prop h_echo_dis h_vote_dis h_ack_dis h_ready_dis h_commit_dis hcp2
  exfalso
  -- Extract invariant components (order differs from Giuliano.lean)
  have inv1 := hinv.2.1
  have inv2 := hinv.2.2.1
  have inv4 := hinv.2.2.2.2.2.2.2.1
  have inv6 := hinv.2.2.2.2.2.2.2.2.1
  have inv7 := hinv.2.2.2.2.2.2.1
  have inv8 := hinv.2.2.2.2.2.2.2.2.2.1
  have inv9 := hinv.2.2.2.2.2.2.2.2.2.2
  have agreement := hinv.2.2.2.2.2.1
  -- Extract assumption components
  have h_bc_cl := has.1
  have h_bc_mj := has.2.1
  obtain ⟨Q_c, hQ_c⟩ := has.2.2.2.1            -- non-faulty commit quorum
  obtain ⟨Q_mf, hQ_mf⟩ := has.2.2.2.2.2.1      -- non-faulty maj quorum
  obtain ⟨Q_cf, hQ_cf⟩ := has.2.2.2.2.2.2.1    -- non-faulty classic quorum
  have h_q_nf := has.2.2.2.2.2.2.2.2.2.2.2.2.1         -- quorum_not_faulty
  have h_amp_nf := has.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1   -- amp_quorum_has_nf_member
  have h_opt_maj := has.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 -- opt_contains_maj (if bc faulty)
  -- p2 hasn't committed any value (by agreement + hcp2)
  have p2_nc : ∀ V', st.committed p2 V' = false := by
    intro V'; by_contra h; simp only [Bool.not_eq_false] at h
    have := agreement p1 p2 v V' hfp1 hfp2 hcp1 h; subst this; grind
  -- From commit_disabled: some member of Q_c not ready for v
  obtain ⟨x₀, hx₀m, hx₀r⟩ := h_commit_dis p2 v hfp2 p2_nc Q_c
  have hx₀nf := hQ_c x₀ hx₀m
  -- Suffices to show x₀ is ready for v (contradicts hx₀r)
  suffices ∀ P, th.faulty P = false → st.ready P v = true by
    exact absurd (this x₀ hx₀nf) (by simp [hx₀r])
  -- Prove all non-faulty parties are ready for v
  intro P hP
  rcases inv1 p1 v hfp1 hcp1 with ⟨Q_a, hQ_a⟩ | ⟨Q_o, hQ_o⟩
  · -- Case (a): amplification quorum Q_a, all non-faulty and ready for v
    by_contra hPnr; simp only [Bool.not_eq_true] at hPnr
    by_cases hPr : ∀ V, st.ready P V = false
    · -- P not ready at all: h_ready_dis + Q_a gives contradiction
      obtain ⟨y, hym, hyr⟩ := (h_ready_dis P v hP hPr).2 Q_a
      exact absurd (hQ_a y hym).2 (by simp [hyr])
    · -- P ready for V' ≠ v: inv4 with Q_a member gives V' = v, contradiction
      push_neg at hPr; obtain ⟨V', hV'⟩ := hPr; simp only [Bool.not_eq_false] at hV'
      obtain ⟨p₀, hp₀nf, hp₀m⟩ := h_amp_nf Q_a
      have := inv4 p₀ P v V' hp₀nf hP (hQ_a p₀ hp₀m).2 hV'
      subst this; grind
  · -- Case (b): opt quorum Q_o, non-faulty members echoed v
    -- Key consequences: non-faulty votes/acks only for v
    have nva := inv6 v Q_o hQ_o   -- non-faulty votes only for v
    have naa := inv8 Q_o v hQ_o   -- non-faulty acks only for v
    -- Step 1: all non-faulty non-broadcasters voted for v
    have all_voted : ∀ P', th.faulty P' = false → P' ≠ th.broadcaster → st.vote P' v = true := by
      intro P' hP' hP'nb; by_contra hno; simp only [Bool.not_eq_true] at hno
      have nv : ∀ V, st.vote P' V = false := by
        intro V; by_cases hVv : V = v
        · subst hVv; exact hno
        · by_contra h; simp only [Bool.not_eq_false] at h; exact absurd (nva P' V hP' h) hVv
      by_cases hbf : th.faulty th.broadcaster = true
      · -- Broadcaster faulty: opt_contains_maj gives maj quorum in Q_o, all echoed v
        obtain ⟨Q_m, hQ_m⟩ := h_opt_maj Q_o hbf
        obtain ⟨y, hym, hyr⟩ := h_vote_dis P' v hP' hP'nb nv Q_m
        exact absurd (hQ_o y (hQ_m y hym).2 (hQ_m y hym).1) (by simp [hyr])
      · -- Broadcaster non-faulty: all non-faulty echoed pv = v
        simp only [Bool.not_eq_true] at hbf
        have h_pv := (inv7 hbf).2 p1 v hfp1 |>.2.2.2.2 hcp1  -- proposal v = true
        obtain ⟨y, hym, hyr⟩ := h_vote_dis P' v hP' hP'nb nv Q_mf
        have hynf := hQ_mf y hym
        have hynb : y ≠ th.broadcaster := by rintro rfl; grind
        by_cases hye : ∀ V, st.echo y V = false
        · exact absurd h_pv (by simp [h_echo_dis y v hynf hynb hye])
        · push_neg at hye; obtain ⟨V', hV'e⟩ := hye; simp only [Bool.not_eq_false] at hV'e
          have hV'eq := (inv7 hbf).1 V' ((inv7 hbf).2 y V' hynf |>.1 hV'e)
          have hveq := (inv7 hbf).1 v h_pv
          rw [hV'eq, ← hveq] at hV'e; grind
    -- Step 2: all non-faulty non-broadcasters acked v
    have all_acked : ∀ P', th.faulty P' = false → P' ≠ th.broadcaster → st.ack P' v = true := by
      intro P' hP' hP'nb; by_contra hno; simp only [Bool.not_eq_true] at hno
      have na : ∀ V, st.ack P' V = false := by
        intro V; by_cases hVv : V = v
        · subst hVv; exact hno
        · exact naa P' V hP' hVv
      obtain ⟨y, hym, hyr⟩ := (h_ack_dis P' v hP' hP'nb na).1 Q_cf
      have hynb : y ≠ th.broadcaster := by rintro rfl; grind
      exact absurd (all_voted y (hQ_cf y hym) hynb) (by simp [hyr])
    -- Step 3: all non-faulty parties readied (and for v)
    by_contra hPnr; simp only [Bool.not_eq_true] at hPnr
    by_cases hPr : ∀ V, st.ready P V = false
    · -- P not ready: h_ready_dis with Q_cf gives y ∈ Q_cf not acked v, contradiction
      obtain ⟨y, hym, hyr⟩ := (h_ready_dis P v hP hPr).1 Q_cf
      have hynb : y ≠ th.broadcaster := by rintro rfl; grind
      exact absurd (all_acked y (hQ_cf y hym) hynb) (by simp [hyr])
    · -- P ready for V': by inv2 + quorum_not_faulty + naa, V' = v, contradiction
      push_neg at hPr; obtain ⟨V', hV'⟩ := hPr; simp only [Bool.not_eq_false] at hV'
      obtain ⟨Q, hQ⟩ := inv2 P V' hP hV'
      obtain ⟨P₃, hP₃nf, hP₃m⟩ := h_q_nf Q
      have hP₃a := hQ P₃ hP₃m hP₃nf
      by_cases hVv : V' = v
      · subst hVv; grind
      · exact absurd hP₃a (by simp [naa P₃ V' hP₃nf hVv])


/--
info: The following set of actions must preserve the invariant and successfully terminate:
  check_totality
    doesNotThrow ... ✅
    inv0 ... ✅
    inv1 ... ✅
    inv2 ... ✅
    inv3 ... ✅
    inv5 ... ✅
    agreement ... ✅
    inv7 ... ✅
    inv4 ... ✅
    inv6 ... ✅
    inv8 ... ✅
    inv9 ... ✅
-/
#guard_msgs in
#check_action check_totality

end OptiRBC
