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

-- TODO suspecting: just `pick` is not desirable, but `pickSuchThat`? also, `pick` then `assume` ≠ `pickSuchThat`?
action send (n next : node) = {
-- action send = {
  -- let n : node ← pick
  -- let next : node ← pick
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  -- let n :| (∃ next, ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z))
  -- let next :| ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := true
}

action recv (sender n next : node) = {
-- action recv = {
  -- let sender : node ← pick
  -- let n : node ← pick
  -- let next : node ← pick
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  -- let sender :| (∃ (n next : node), ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z))
  -- let n :| (∃ (next : node), ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z))
  -- let next :| ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
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

instance between_ℤ_ring' (l : List Nat) (hnodup : List.Nodup l) : Between (Fin l.length) :=
  between_ℤ_ring (Fin _) l.get (by
    intro ⟨a, ha⟩ ⟨b, hb⟩ h1 ; simp at * ; rw [List.Nodup.getElem_inj_iff hnodup] ; assumption)

instance between_ℤ_ring'' (n : Nat) (l : List Nat) (hlength : l.length = n) (hnodup : List.Nodup l) : Between (Fin n) := by
  have a := between_ℤ_ring' l hnodup
  rw [hlength] at a ; exact a

veil module Ring2

variable [Fintype node] [insta : DecidableRel tot.le]
variable [instb : ∀ a b c, Decidable (btwn.btw a b c)]

#gen_executable

-- #check Lean.
-- #check Plausible.Gen

end Ring2

section tmp

variable (n : Nat)    -- TODO parameter not supported ???

-- #deriveGen (Ring2.Label (Fin n))
#deriveGen (Ring2.Label (Fin 5))

end tmp

def simple_init (l : List Nat) (hl : l ≠ []) (hnodup : List.Nodup l) :=
  Ring2.InitActExec (Fin l.length) (node_ne := by rw [← Fin.pos_iff_nonempty, List.length_pos_iff] ; exact hl)
    (btwn := between_ℤ_ring' l hnodup) (tot := by infer_instance)
    (σ := Ring2.State _) (ρ := Ring2.Reader _)
    (insta := by dsimp [TotalOrder.le] ; infer_instance)
    (instb := by intro a b c ; dsimp [Between.btw, between_ℤ_ring', between_ℤ_ring] ; infer_instance)

def simple_run (l : List Nat) (hl : l ≠ []) (hnodup : List.Nodup l) :=
  Ring2.NextActExec (Fin l.length) (node_ne := by rw [← Fin.pos_iff_nonempty, List.length_pos_iff] ; exact hl)
    (btwn := between_ℤ_ring' l hnodup) (tot := by infer_instance)
    (σ := Ring2.State _) (ρ := Ring2.Reader _)
    (insta := by dsimp [TotalOrder.le] ; infer_instance)
    (instb := by intro a b c ; dsimp [Between.btw, between_ℤ_ring', between_ℤ_ring] ; infer_instance)

-- set_option maxSynthPendingDepth 10
-- set_option synthInstance.maxHeartbeats 1000000
-- set_option synthInstance.maxSize 1000

instance : Inhabited (Ring2.Reader (Fin n)) := ⟨Ring2.Reader.mk⟩
instance : Inhabited (Ring2.State (Fin n)) := ⟨Ring2.State.mk default default⟩

def DivM.run (a : DivM α) :=
  match a with
  | .res x => Option.some x
  | .div => Option.none

-- TODO why system cannot be synthesized here? due to `btwn`???
def simple_check (l : List Nat) (hl : l.length = 5) (hnodup : List.Nodup l)
    (steps : Nat) (cfg : Plausible.Configuration) :=
  @check_safety _ _ (labType := (Ring2.Label (Fin 5)))
    (sys := Ring2.System _ (btwn := between_ℤ_ring'' _ l hl hnodup) (Ring2.State _) (Ring2.Reader _)) Ring2.Label.gen
    (by
      have a := (simple_run l (by rw [← List.length_pos_iff, hl] ; decide) hnodup)
      rw [hl] at a ; exact a)
    ⟨⟩
    (by
      have a := (simple_init l (by rw [← List.length_pos_iff, hl] ; decide) hnodup)
      rw [hl] at a
      exact DivM.run (a default default) |>.get!.getD (fun _ => default) |>.2)
    steps cfg
    -- NOTE: seems need to unfold a bunch of things before going through
    (by
      intro r s
      dsimp [invSimp] ; dsimp [TotalOrder.le] ; infer_instance)

section abc

-- `l[i]`: the node `i` is at position `l[i]`
local macro "l" : term => `(term| ([1, 3, 5, 4, 2]))

local macro "test_state_1" : term => `(term| @Ring2.State.mk (Fin 5) (fun _ => false)
  (fun i j => (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 1) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 2 ∧ j = 0)))

local macro "initstate" : term => `(term| @Ring2.State.mk (Fin 5) (fun _ => false)
  (fun _ _ => false))

local macro "initreader" : term => `(term| Ring2.Reader.mk )

example [tot : TotalOrder _] [btwn : Between _] :
  letI sys := Ring2.System (Fin 5) (tot := tot) (btwn := btwn) (Ring2.State _) (Ring2.Reader _)
  sys.assumptions initreader ∧ sys.init initreader initstate := by
  dsimp [initSimp, invSimp] ; simp

#eval (simple_init l (by decide) (by decide)
      |>.run initreader |>.run test_state_1 |>.run |>.run
      |>.getD (Except.ok <| ((), test_state_1)) |>.getD (fun _ => ((), test_state_1))
      |>.snd |>.pending 0 4)

#eval (simple_run l (by decide) (by decide)
    (Ring2.Label.recv ⟨0, by decide⟩ ⟨4, by decide⟩ ⟨1, by decide⟩)
      |>.run initreader |>.run test_state_1 |>.run |>.run
      |>.getD (Except.ok <| ((), test_state_1)) |>.getD (fun _ => ((), test_state_1))
      |>.snd |>.pending 0 4)


#eval show IO Unit from do
  let res ← simple_check l (by decide) (by decide) 10000
    ({} : Plausible.Configuration) |>.run 1000000
  let b := res.safe?
  IO.println s!"{b}"
  unless b do
    panic! "Safety check failed"

end abc
