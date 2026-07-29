namespace Veil

/-- Generate all possible mappings from a list of keys to values. -/
def allMappings (keys : List α) (vals : List β) : List (List (α × β)) :=
  match keys with
  | [] => [[]]
  | k :: ks =>
    let rest := allMappings ks vals
    (vals.map (fun v => rest.map (fun m => (k, v) :: m))).flatten

/-- Membership characterization for `allMappings`. -/
theorem mem_allMappings_iff {keys : List α} {vals : List β} {m : List (α × β)} :
    m ∈ allMappings keys vals ↔ m.map Prod.fst = keys ∧ ∀ p ∈ m, p.2 ∈ vals := by
  induction keys generalizing m with
  | nil => simp [allMappings]; intro h; subst h; simp
  | cons k ks ih =>
    simp only [allMappings, List.mem_flatten, List.mem_map]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, hm⟩
      simp only [List.mem_map] at hm
      obtain ⟨m', hm', rfl⟩ := hm
      simp only [ih] at hm'
      simp only [List.map_cons, List.cons.injEq, true_and, List.mem_cons, forall_eq_or_imp]
      exact ⟨hm'.1, hv, hm'.2⟩
    · rintro ⟨hkeys, hvals⟩
      match m with
      | [] => simp_all
      | (a, b) :: ps =>
        simp only [List.map_cons, List.cons.injEq] at hkeys
        refine ⟨_, ⟨b, hvals _ (.head _), rfl⟩, List.mem_map.mpr ⟨ps, ih.mpr ⟨hkeys.2, fun q hq => hvals q (.tail _ hq)⟩, by simp [hkeys.1]⟩⟩

theorem allMappings_complete {keys : List α} {vals : List β} :
    ∀ k v, k ∈ keys → v ∈ vals → (k, v) ∈ (allMappings keys vals).flatten := by
  intro k v hk hv
  let m := keys.map (fun k' => (k', v))
  have hm : m ∈ allMappings keys vals :=
    mem_allMappings_iff.mpr ⟨by simp [m, Function.comp_def], by simp [m, hv]⟩
  exact List.mem_flatten.mpr ⟨m, hm, List.mem_map.mpr ⟨k, hk, rfl⟩⟩

end Veil
