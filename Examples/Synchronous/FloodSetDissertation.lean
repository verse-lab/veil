import Veil

-- Version of FloodSet from George's dissertation

veil module FloodSet

type node
type value
instantiate val_ord : TotalOrder value

immutable individual f : Nat                        -- maximum number of crash failures

individual round : Nat                              -- current round number (0 to f+1)
function initialValue : node → value                -- initial proposal for each node
relation W (n : node) (v : value) : Bool            -- W set per node
relation decision (n : node) (v : value) : Bool     -- decision value per node, initially ∅
function crashed (n : node) : Bool                  -- has this node crashed?
function crashedInRound (n : node) : Nat            -- which round did it crash in?
individual numCrashed : Nat                         -- total number of crashes so far

ghost relation alive (n : node) := ¬crashed n
ghost relation crashedInAPreviousRound (n : node) := (crashed n ∧ crashedInRound n < round)

after_init {
  initialValue := *
  round := 0
  W N V := (V == initialValue N)
  decision N V := false
  crashed N := false
  crashedInRound N := 0
  numCrashed := 0
}

action crash (n : node) {
  require numCrashed < f
  require alive n
  crashed n := true
  crashedInRound n := round
  numCrashed := numCrashed + 1
}

action advanceRound {
  require round < f + 1
  -- We model message delivery by picking a delivery relation that determines
  -- which messages from each sender are received by which receivers.
  let delivery : (node → node → Bool) :|
    (∀ (sender : node),
      (crashedInAPreviousRound sender → (∀ (receiver : node), ¬ delivery sender receiver)) ∧
      (alive sender → (∀ (receiver : node), delivery sender receiver)))
  -- A node knows a value at the end of this round iff it either already knew it,
  -- or received it from some sender that knew it.
  W N V := decide $ W N V ∨ (alive N ∧ ∃ sender, delivery sender N ∧ W sender V)
  round := round + 1
}

procedure deterministicDecision (n : node) {
  let v ← pick value
  assume W n v ∧ (∀ v', W n v' → val_ord.le v v')
  return v
}

action nodeDecide (n : node) {
  require round = f + 1
  require alive n
  require ¬(∃ v, decision n v)
  let v ← deterministicDecision n
  decision n v := true
}

safety [agreement]
  ∀ n₁ n₂ v₁ v₂, decision n₁ v₁ ∧ decision n₂ v₂ → v₁ = v₂

safety [strong_validity]
  ∀ n v, decision n v → ((∃ m, initialValue m = v))

invariant [every_seen_is_someones_initial]
  ∀ n v, W n v → (∃ m, initialValue m = v)

invariant [decision_minimum_seen]
  ∀ n v, decision n v → (∀ v', W n v' → val_ord.le v v')

invariant [crash_limit]
  numCrashed ≤ f

invariant [no_crashes_def]
  numCrashed = 0 ↔ ∀ n, ¬ crashed n

invariant [decision_crashed_after_end]
  ∀ n v, (decision n v ∧ crashed n) → crashedInRound n ≥ f + 1

invariant [decision_only_at_end]
  ∀ n v, decision n v → round ≥ f + 1

invariant [crashed_in_round_le_round]
  ∀ n, crashedInRound n ≤ round

invariant [initial_value_in_W]
  ∀ n, W n (initialValue n)

invariant [decided_in_seen]
  ∀ n v, decision n v → W n v

invariant [crashedInRound_default]
  ∀ n, alive n → crashedInRound n = 0

ghost relation crashedNow (n : node) := crashed n ∧ crashedInRound n = round
ghost relation roundParticipant (n : node) := alive n ∨ crashedNow n
ghost relation crashFreeRound (r : Nat) :=
  ∀ n, ¬ crashed n ∨ crashedInRound n ≠ r
ghost relation hadCrashFreeRound := ∃ r, r < round ∧ crashFreeRound r

invariant [crash_round_gap]
  numCrashed < round → hadCrashFreeRound

invariant [crash_round_gap_or_current]
  numCrashed = round → hadCrashFreeRound ∨ crashFreeRound round

invariant [participants_have_equal_W_after_crash_free]
  hadCrashFreeRound → ∀ n₁ n₂ v, roundParticipant n₁ ∧ roundParticipant n₂ → (W n₁ v = W n₂ v)

#gen_spec

#model_check { node := Fin 3, value := Fin 3 } { f := 3 }

#check_invariants

@[veil]
theorem nodeDecide_agreement (ρ : Type) (σ : Type) (node : Type) [node_dec_eq : DecidableEq.{1} node]
    [node_inhabited : Inhabited.{1} node] (value : Type) [value_dec_eq : DecidableEq.{1} value]
    [value_inhabited : Inhabited.{1} value] [val_ord : TotalOrder value] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain node value __veil_f) (State.Label.toCodomain node value __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain node value __veil_f)
          (State.Label.toCodomain node value __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory node value) ρ]
    [nodeDecide_dec_0 : delta% @FloodSet.nodeDecide._veil_dec_type_0 node χ value χ_rep]
    [nodeDecide_dec_1 : delta% @FloodSet.nodeDecide._veil_dec_type_1 node χ value χ_rep val_ord] :
    ∀ (n : node),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@nodeDecide.ext ρ σ node node_dec_eq node_inhabited value value_dec_eq value_inhabited val_ord χ χ_rep
          χ_rep_lawful σ_sub ρ_sub nodeDecide_dec_0 nodeDecide_dec_1 n)
        (@Assumptions ρ node node_dec_eq node_inhabited value value_dec_eq value_inhabited val_ord ρ_sub)
        (@Invariants ρ σ node node_dec_eq node_inhabited value value_dec_eq value_inhabited val_ord χ χ_rep χ_rep_lawful
          σ_sub ρ_sub)
        (@agreement ρ σ node node_dec_eq node_inhabited value value_dec_eq value_inhabited val_ord χ χ_rep χ_rep_lawful
          σ_sub ρ_sub) :=
  by
  unveil
  rcases hinv with
    ⟨hagree, _, _, hdecision_min, hcrash_limit, _, hdecision_crashed_after_end, _,
      hcrashed_le_round, _, hdecided_in_seen, _, hcrash_round_gap, _, hparticipants_equal⟩
  intro hround halive hnodec t hWt hmin n₁ n₂ v₁ v₂ hdec₁ hdec₂
  -- By pigeonhole: `f+1` rounds with at most `f` crashes gives a crash-free round.
  obtain ⟨r, hr_lt, hcrash_free⟩ := hcrash_round_gap (by rw [hround]; omega)
  -- A node that decided must still be a round participant (alive or crashed this round).
  have hpart {m : node} {v : value} (hdec : st.decision m v = true) :
      st.crashed m = false ∨ st.crashed m = true ∧ st.crashedInRound m = st.round := by
    by_cases hcr : st.crashed m = true
    · refine .inr ⟨hcr, ?_⟩
      have := hdecision_crashed_after_end m v hdec hcr
      have := hcrashed_le_round m; rw [hround] at *; omega
    · exact .inl (by grind)
  -- After the crash-free round, all participants have identical `W` sets,
  -- so any old decided value must equal the minimum `t` chosen by `n`.
  have old_eq_t {m : node} {v : value} (hdec : st.decision m v = true) : v = t := by
    have hn_part : st.crashed n = false ∨ st.crashed n = true ∧ st.crashedInRound n = st.round
      := .inl halive
    have hm_part := hpart hdec
    exact @TotalOrder.le_antisymm value val_ord v t
      (hdecision_min m v hdec t (by simpa [(hparticipants_equal r hr_lt hcrash_free m n t
        hm_part hn_part)] using hWt))
      (hmin v (by simpa [(hparticipants_equal r hr_lt hcrash_free m n v
        hm_part hn_part)] using
        hdecided_in_seen m v hdec))
  -- In the post-state, each decision is either the new `(n, t)` or an old one.
  have new_or_old {m : node} {v : value}
      (hdec : (n = m → ¬ t = v) → st.decision m v = true) :
      (n = m ∧ t = v) ∨ st.decision m v = true := by
    by_cases hnm : n = m
    · exact (em (t = v)).elim (fun h => .inl ⟨hnm, h⟩) (fun h => .inr (hdec fun _ => h))
    · exact .inr (hdec fun h => absurd h hnm)
  -- Every post-state decision value equals `t`: new ones by definition, old ones by `old_eq_t`.
  have all_eq_t {m v} (hdec : (n = m → ¬ t = v) → st.decision m v = true) : v = t := by
    rcases new_or_old hdec with ⟨_, rfl⟩ | hold
    · rfl
    · exact old_eq_t hold
  exact (all_eq_t hdec₁).trans (all_eq_t hdec₂).symm

end FloodSet
