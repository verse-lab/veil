import Veil.Std
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Nodup

-- some commonly used things during extraction

instance Fin.pos_then_inhabited {n : Nat} (h : 0 < n) : Inhabited (Fin n) where
  default := Fin.mk 0 h

instance (n : Nat) : TotalOrder (Fin n) where
  le := fun x y => x.val ≤ y.val
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega

/-- A rank-based ring topology, where each node is assigned with a unique `Nat` rank,
    nodes are sorted by their ranks, and the ring is formed by connecting the sorted
    list of nodes. -/
instance between_ring (node : Type) [DecidableEq node] (f : node → Nat)
  (h : ∀ n1 n2, n1 ≠ n2 → f n1 ≠ f n2) : Between node where
  btw := fun a b c => (f a < f b ∧ f b < f c) ∨ (f c < f a ∧ f a < f b) ∨ (f b < f c ∧ f c < f a)
  btw_ring := by aesop
  btw_trans := by omega
  btw_side := by omega
  btw_total := by
    intro a b c
    by_cases h1 : a = b ; subst_vars ; simp
    by_cases h2 : a = c ; subst_vars ; simp
    by_cases h3 : b = c ; subst_vars ; simp
    have hh1 := h _ _ h1 ; have hh2 := h _ _ h2 ; have hh3 := h _ _ h3
    omega

instance between_ring' (l : List Nat) (hnodup : List.Nodup l) : Between (Fin l.length) :=
  between_ring (Fin _) l.get (by
    intro ⟨a, ha⟩ ⟨b, hb⟩ h1 ; simp at * ; rw [List.Nodup.getElem_inj_iff hnodup] ; assumption)

instance between_ring'' (n : Nat) (l : List Nat) (hlength : l.length = n) (hnodup : List.Nodup l) : Between (Fin n) := by
  have a := between_ring' l hnodup
  rw [hlength] at a ; exact a
