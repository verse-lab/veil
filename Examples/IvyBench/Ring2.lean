import Veil
import Veil.DSL.Random.Extract
import Veil.DSL.Random.Main

-- https://github.com/aman-goel/ivybench/blob/5db7eccb5c3bc2dd14dfb58eddb859b036d699f5/ex/ivy/ring.ivy

veil module Ring2


type node
instantiate tot : TotalOrder node
instantiate btwn : Between node


open Between TotalOrder

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

action send (n next : node) = {
  -- let n : node ← pick
  -- let next : node ← pick
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := true
}

action recv (sender n next : node) = {
-- action recv = {
  -- let sender : node ← pick
  -- let n : node ← pick
  -- let next : node ← pick
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  -- message may or may not be removed
  -- this models that multiple messages might be in flight
  pending sender n := *
  if (sender = n) then
    leader n := true
  else
    -- pass message to next node
    if (le n sender) then
      pending sender next := true
}

safety [single_leader] leader L → le N L
invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#gen_spec

-- #time #check_invariants

end Ring2

instance (n : Nat) : TotalOrder (Fin n) where
  le := fun x y => x.val ≤ y.val
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega

instance between_ℤ_ring (node : Type) [DecidableEq node] [Fintype node] (f : node → Nat)
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

def between_ℤ_ring' (l : List Nat) (hnodup : List.Nodup l) : Between (Fin l.length) :=
  between_ℤ_ring (Fin _) l.get (by
    intro ⟨a, ha⟩ ⟨b, hb⟩ h1 ; simp at * ; rw [List.Nodup.getElem_inj_iff hnodup] ; assumption)

veil module Ring2

variable [Fintype node] [insta : DecidableRel tot.le]
variable [instb : ∀ a b c, Decidable (btwn.btw a b c)]

#gen_executable

end Ring2

def simple_run (l : List Nat) (hl : l ≠ []) (hnodup : List.Nodup l) :=
  Ring2.NextActExec (Fin l.length) (node_ne := by rw [← Fin.pos_iff_nonempty, List.length_pos_iff] ; exact hl)
    (btwn := between_ℤ_ring' l hnodup) (tot := by infer_instance)
    (σ := Ring2.State _) (ρ := Ring2.Reader _)
    (insta := by dsimp [TotalOrder.le] ; infer_instance)
    (instb := by intro a b c ; dsimp [Between.btw, between_ℤ_ring', between_ℤ_ring] ; infer_instance)

section abc

-- `l[i]`: the node `i` is at position `l[i]`
local macro "l" : term => `(term| ([1, 3, 5, 4, 2]))

local macro "initstate" : term => `(term| @Ring2.State.mk (Fin 5) (fun _ => false)
  (fun i j => (i = 0 ∧ j = 4) ∨ (i = 4 ∨ j = 1) ∨ (i = 1 ∨ j = 3) ∨ (i = 3 ∨ j = 2) ∨ (i = 2 ∨ j = 0)))

def DivM.run (a : DivM α) :=
  match a with
  | .res x => Option.some x
  | .div => Option.none

#eval (simple_run l (by decide) (by decide)
    (Ring2.Label.recv ⟨0, by decide⟩ ⟨4, by decide⟩ ⟨1, by decide⟩)
      |>.run Ring2.Reader.mk |>.run initstate |>.run |>.run
      |>.getD (Except.ok <| ((), initstate)) |>.getD (fun _ => ((), initstate))
      |>.snd |>.pending 0 4)

end abc
