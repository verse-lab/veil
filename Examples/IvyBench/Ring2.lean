import Veil
import Veil.DSL.Random.ExtractUtil
import Veil.DSL.Random.Extract
import Veil.DSL.Random.Main

-- https://github.com/aman-goel/ivybench/blob/5db7eccb5c3bc2dd14dfb58eddb859b036d699f5/ex/ivy/ring.ivy

veil module Ring2


type node
instantiate tot : TotalOrder node
instantiate btwn : Between node
-- instantiate repr : ToString node


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

-- action send = {
--   let ((n : node), next) :| ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
--   dbg_trace s!"{n} {next}"
--   pending n next := true
-- }


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
  let lock <- pick Bool
  pending sender n := lock
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

veil module Ring2

variable [FinEnum node] [insta : DecidableRel tot.le]
variable [instb : ∀ a b c, Decidable (btwn.btw a b c)]

-- instance [Fintype node] : Plausible.SampleableExt (node × node) := by
  -- apply @Plausible.Prod.sampleableExt

attribute [-instance] instFindableOfFinEnumOfDecidablePred

#gen_executable

simple_deriving_repr_for State

#print nextActExec

end Ring2

#deriveGen Ring2.Label

def simple_init (l : List Nat) (hl : 0 < l.length) (hnodup : List.Nodup l) :=
  Ring2.initExec (Fin l.length) (node_ne := by
    refine ⟨0, hl⟩)
    (btwn := between_ring' l hnodup) (tot := by infer_instance)
    (σ := Ring2.State _) (ρ := Ring2.Reader _)
    (insta := by dsimp [TotalOrder.le] ; infer_instance)
    (instb := by intro a b c ; dsimp [Between.btw, between_ring', between_ring] ; infer_instance)

def simple_run (l : List Nat) (hl : 0 < l.length) (hnodup : List.Nodup l) :=
  Ring2.nextActExec (Fin l.length) (node_ne := by
    refine ⟨0, hl⟩)
    (btwn := between_ring' l hnodup) (tot := by infer_instance)
    (σ := Ring2.State _) (ρ := Ring2.Reader _)
    (insta := by dsimp [TotalOrder.le] ; infer_instance)
    (instb := by intro a b c ; dsimp [Between.btw, between_ring', between_ring] ; infer_instance)

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
    (sys := Ring2.System _ (btwn := between_ring'' _ l hl hnodup) (Ring2.State _) (Ring2.Reader _)) Ring2.Label.gen
    (by
      have a := (simple_run l (by rw [hl];decide) hnodup)
      rw [hl] at a ; exact a)
    ⟨⟩
    (by
      have a := (simple_init l (by rw [hl] ; decide) hnodup)
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
      |>.snd |>.pending 0 4
      )

deriving instance Repr for Ring2.Label
deriving instance Repr for Ring2.Reader

#eval simple_check l (by decide) (by decide) 100
    ({ numRetries := 1000, numInst := 10000 } : Plausible.Configuration) |>.run 1000

end abc
