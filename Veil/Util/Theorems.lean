import Veil.Frontend.DSL.State.Types

namespace Veil

abbrev IteratedPred := IteratedArrow Prop

def IteratedPred.forall {ts : List Type}
  (f : IteratedPred ts) : Prop :=
  match ts with
  | [] => f
  | _ :: _ => ∀ x, IteratedPred.forall (f x)

def IteratedPred.exists {ts : List Type}
  (f : IteratedPred ts) : Prop :=
  match ts with
  | [] => f
  | _ :: _ => ∃ x, IteratedPred.exists (f x)

def IteratedPred.forallImplies {ts : List Type}
  (f g : IteratedPred ts) : Prop :=
  match ts with
  | [] => (f → g)
  | _ :: _ => ∀ x, IteratedPred.forallImplies (f x) (g x)

def repeatedOrProp (ps : List ((ts : List Type) × IteratedPred ts)) : Prop :=
  match ps.reverse with
  | [] => False
  | ⟨_, p1⟩ :: psr => psr.reverse.foldr (init := p1.exists) fun ⟨_, p⟩ => Or p.exists

private def repeatedOrPropSimple (ps : List ((ts : List Type) × IteratedPred ts)) : Prop :=
  ps.foldr (init := False) fun ⟨_, p⟩ => Or p.exists

theorem repeatedOrProp_eq_repeatedOrPropSimple (ps : List ((ts : List Type) × IteratedPred ts)) :
  repeatedOrProp ps ↔ repeatedOrPropSimple ps := by
  rcases h : ps.reverse with _ | ⟨⟨_, p⟩, pss⟩
  · simp at h ; subst ps ; rfl
  · dsimp [repeatedOrProp, repeatedOrPropSimple]
    rw [h] ; dsimp
    have htmp := congrArg List.reverse h
    simp at htmp
    clear h ; subst ps ; simp

theorem IteratedPred.exists_implies (ts : List Type) (p1 p2 : IteratedPred ts)
  (h : p1.forallImplies p2) : p1.exists → p2.exists := by
  induction ts with
  | nil => exact h
  | cons t ts ih =>
    dsimp [IteratedPred.exists, IteratedPred.forallImplies] at *
    rintro ⟨x, h1⟩ ; specialize ih _ _ (h x) h1 ; exists x

theorem IteratedPred.bigor_exists_implies (ps : List ((ts : List Type) × (IteratedPred ts × IteratedPred ts)))
  (h : ps.foldr (init := True) fun ⟨_, (p1, p2)⟩ => And <| p1.forallImplies p2)
  (idxs : List (Fin ps.length)) :
  letI ps1 := idxs.map fun i => let ⟨ts, (p1, _)⟩ := ps[i] ; Sigma.mk ts p1
  letI ps2 := idxs.map fun i => let ⟨ts, (_, p2)⟩ := ps[i] ; Sigma.mk ts p2
  repeatedOrProp ps1 → repeatedOrProp ps2 := by
  simp only [repeatedOrProp_eq_repeatedOrPropSimple]
  induction idxs with
  | nil => simp [repeatedOrPropSimple]
  | cons idx idxs ih =>
    dsimp [repeatedOrPropSimple]
    intro h ; rcases h with h | h
    · left ; revert h ; apply IteratedPred.exists_implies
      rcases idx with ⟨idx, hidx⟩ ; dsimp
      clear *- h
      have hin := List.mem_of_getElem (i := idx) (h := hidx) (a := ps[idx]'hidx) rfl
      generalize ps[idx] = p at * ; clear idx hidx
      rcases p with ⟨ts, ⟨p1, p2⟩⟩ ; dsimp
      induction ps with
      | nil => simp at hin
      | cons p ps ih =>
        simp at h ; rcases h with ⟨hp, h⟩
        simp at hin ; rcases hin with hin | hin
        · subst p ; exact hp
        · specialize ih h hin ; exact ih
    · right ; revert h ; apply ih

end Veil
